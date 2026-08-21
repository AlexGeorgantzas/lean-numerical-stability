# Declaration dossier for P16-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t3_mixed_precision_geometric_convergence
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (run : P16MixedPrecisionGMRESRun (n := n) l)
    (hLambda : p16MuchLessThanOneAt l (p16MixedContraction run)) :
    (∀ i : ℕ,
      p16FirstOrderLeAt l (p16MixedScale run)
        (fun t ↦ p16BackwardError run.A run.b (run.xHat (i + 1) t))
        (fun t ↦
          p16MixedContraction run t *
              p16BackwardError run.A run.b (run.xHat i t) +
            p16BackwardFloor run t)) ∧
      ∀ i : ℕ,
        p16FirstOrderLeAt l (p16MixedScale run)
          (fun t ↦ p16ForwardError run.xExact (run.xHat (i + 1) t))
          (fun t ↦
            p16MixedContraction run t *
                p16ForwardError run.xExact (run.xHat i t) +
              p16ForwardFloor run t)
```

## Elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (run : HighamBench.P16MixedPrecisionGMRESRun l),
  HighamBench.p16MuchLessThanOneAt l (HighamBench.p16MixedContraction run) →
    And
      (∀ (i : Nat),
        HighamBench.p16FirstOrderLeAt l (HighamBench.p16MixedScale run)
          (fun t => HighamBench.p16BackwardError run.A run.b (run.xHat (instHAdd.hAdd i 1) t)) fun t =>
          instHAdd.hAdd
            (instHMul.hMul (HighamBench.p16MixedContraction run t)
              (HighamBench.p16BackwardError run.A run.b (run.xHat i t)))
            (HighamBench.p16BackwardFloor run t))
      (∀ (i : Nat),
        HighamBench.p16FirstOrderLeAt l (HighamBench.p16MixedScale run)
          (fun t => HighamBench.p16ForwardError run.xExact (run.xHat (instHAdd.hAdd i 1) t)) fun t =>
          instHAdd.hAdd
            (instHMul.hMul (HighamBench.p16MixedContraction run t)
              (HighamBench.p16ForwardError run.xExact (run.xHat i t)))
            (HighamBench.p16ForwardFloor run t))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (run : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l)
  (hLambda : @HighamBench.p16MuchLessThanOneAt.{u_1} ι l (@HighamBench.p16MixedContraction.{u_1} n ι l run)),
  And
    (∀ (i : Nat),
      @HighamBench.p16FirstOrderLeAt.{u_1} ι l (@HighamBench.p16MixedScale.{u_1} n ι l run)
        (fun (t : ι) =>
          @HighamBench.p16BackwardError n (@HighamBench.P16MixedPrecisionGMRESRun.A.{u_1} n ι l run)
            (@HighamBench.P16MixedPrecisionGMRESRun.b.{u_1} n ι l run)
            (@HighamBench.P16MixedPrecisionGMRESRun.xHat.{u_1} n ι l run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t))
        fun (t : ι) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16MixedContraction.{u_1} n ι l run t)
            (@HighamBench.p16BackwardError n (@HighamBench.P16MixedPrecisionGMRESRun.A.{u_1} n ι l run)
              (@HighamBench.P16MixedPrecisionGMRESRun.b.{u_1} n ι l run)
              (@HighamBench.P16MixedPrecisionGMRESRun.xHat.{u_1} n ι l run i t)))
          (@HighamBench.p16BackwardFloor.{u_1} n ι l run t))
    (∀ (i : Nat),
      @HighamBench.p16FirstOrderLeAt.{u_1} ι l (@HighamBench.p16MixedScale.{u_1} n ι l run)
        (fun (t : ι) =>
          @HighamBench.p16ForwardError n (@HighamBench.P16MixedPrecisionGMRESRun.xExact.{u_1} n ι l run)
            (@HighamBench.P16MixedPrecisionGMRESRun.xHat.{u_1} n ι l run
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t))
        fun (t : ι) =>
        @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HighamBench.p16MixedContraction.{u_1} n ι l run t)
            (@HighamBench.p16ForwardError n (@HighamBench.P16MixedPrecisionGMRESRun.xExact.{u_1} n ι l run)
              (@HighamBench.P16MixedPrecisionGMRESRun.xHat.{u_1} n ι l run i t)))
          (@HighamBench.p16ForwardFloor.{u_1} n ι l run t))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P16Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P16Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P16MixedPrecisionGMRESRun`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `51458db0c51de2a96234380865d7469752042444011e63ace5bdf3c17f32d9b6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → Filter ι → Type u_1
```

Fully explicit type:

```lean
{n : Nat} → {ι : Type u_1} → (l : Filter.{u_1} ι) → Type u_1
```

### D002: `HighamBench.P16MixedPrecisionGMRESRun.A`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e28b6875676e8c359449b7668ee15841cc9217b6d7aa2aa89366e84c7f084b2b`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → HighamBench.P16Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → HighamBench.P16Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.2
```

### D003: `HighamBench.P16MixedPrecisionGMRESRun.b`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ae1e650774899a6ecd2d298fd6fa794cef6f1a7c999865bd394783ae8b14263f`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.4
```

### D004: `HighamBench.P16MixedPrecisionGMRESRun.xExact`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `e41083c321cb651d26a8bb2b9ca8a11ac8b5d2c3fc2cb48821271a48185307e6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.5
```

### D005: `HighamBench.P16MixedPrecisionGMRESRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1f967da311d03daf58abaca30d28927dfff89a9bdb8380a8194642062c68e885`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → Nat → ι → HighamBench.P16Vector n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → Nat → ι → HighamBench.P16Vector n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.6
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

### D007: `HighamBench.p16BackwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1dd328aa23f56f00539a1a671c1678b407df7d8674c99cfd90b802e239733cc6`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t => instHMul.hMul (HighamBench.p16PolynomialFactorValue run.polynomialFactor n n) (run.uHigh t)
```

### D008: `HighamBench.p16FirstOrderLeAt`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f8fb89f45dff8ea408faebbf7940e52c3a8135ec7c9fa4489c8e3a8540da3a7b`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale lhs rhs : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale lhs rhs =>
  Exists fun remainder =>
    And (HighamBench.p16SecondOrderAt l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D009: `HighamBench.p16ForwardError`

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

### D010: `HighamBench.p16ForwardFloor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `07175b6eeecdc25ff174e86e12050da2978093bef10bace3dedfda70c0cd784c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHMul.hMul (instHMul.hMul (HighamBench.p16PolynomialFactorValue run.polynomialFactor n n) (run.uHigh t))
    (HighamBench.p16ConditionNumberF run.A run.Ainv)
```

### D011: `HighamBench.p16MixedContraction`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5c7c6465ffab9f805655532e5a5e83bf1d168c08e878480078fcd2231bc1612e`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t =>
  instHMul.hMul (instHMul.hMul (HighamBench.p16PolynomialFactorValue run.polynomialFactor n n) (run.uLow t))
    (HighamBench.p16ConditionNumberF run.A run.Ainv)
```

### D012: `HighamBench.p16MixedScale`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `708175afe78342782c0fbd8b99965642cc8024089ae16c33ecc907c016c35eb9`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} {ι} {l} run t => instHAdd.hAdd (run.uHigh t) (run.uLow t)
```

### D013: `HighamBench.p16MuchLessThanOneAt`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe11d8a7495ed132c0b3333870c07122ca62d29111e5137f4d42ebb136cb2426`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (lambda : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l lambda =>
  And (Filter.Tendsto lambda l (nhds 0))
    (Filter.Eventually (fun t => And (Real.instLE.le 0 (lambda t)) (Real.instLT.lt (lambda t) 1)) l)
```

### D014: `HighamBench.P16Matrix`

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

### D015: `HighamBench.P16MixedPrecisionGMRESRun.Ainv`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `270eda0230af7580e6c1ae66307da68ad740caeb9f4491043cdfacc50e84490c`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → HighamBench.P16Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → HighamBench.P16Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.3
```

### D016: `HighamBench.P16MixedPrecisionGMRESRun.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `2d46d32f1d8eb2ec8801d0d21371249e7112ad81d62c1f331dc43292124ddec6`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      instLTNat.lt 0 n →
        (A Ainv : HighamBench.P16Matrix n) →
          (b xExact : HighamBench.P16Vector n) →
            (xHat residualHat correctionHat residualError updateError : Nat → ι → HighamBench.P16Vector n) →
              (uHigh uLow : ι → Real) →
                (polynomialFactor : HighamBench.P16PolynomialFactor) →
                  Ne b 0 →
                    HighamBench.p16IsNonsingular A →
                      (∀ (z : HighamBench.P16Vector n), Eq (HighamBench.p16MatVec Ainv (HighamBench.p16MatVec A z)) z) →
                        (∀ (z : HighamBench.P16Vector n),
                            Eq (HighamBench.p16MatVec A (HighamBench.p16MatVec Ainv z)) z) →
                          Eq (HighamBench.p16MatVec A xExact) b →
                            (∀ (t : ι), Real.instLE.le 0 (uHigh t)) →
                              (∀ (t : ι), Real.instLE.le 0 (uLow t)) →
                                (∀ (t : ι), Real.instLE.le (uHigh t) (uLow t)) →
                                  Filter.Tendsto uHigh l (nhds 0) →
                                    Filter.Tendsto uLow l (nhds 0) →
                                      (∀ (t : ι), HighamBench.GammaValid (uHigh t) n) →
                                        (∀ (i : Nat) (t : ι),
                                            Eq (residualHat i t)
                                              (instHAdd.hAdd (HighamBench.p16Residual A b (xHat i t))
                                                (residualError i t))) →
                                          (∀ (i : Nat) (t : ι) (j : Fin n),
                                              Real.instLE.le (abs (residualError i t j))
                                                (instHMul.hMul (HighamBench.gamma (uHigh t) n)
                                                  (instHAdd.hAdd (abs (b j))
                                                    (HighamBench.p16MatVec (fun row col => abs (A row col))
                                                      (fun col => abs (xHat i t col)) j)))) →
                                            (∀ (i : Nat) (t : ι),
                                                Eq (xHat (instHAdd.hAdd i 1) t)
                                                  (instHAdd.hAdd (instHAdd.hAdd (xHat i t) (correctionHat i t))
                                                    (updateError i t))) →
                                              (∀ (i : Nat) (t : ι) (j : Fin n),
                                                  Real.instLE.le (abs (updateError i t j))
                                                    (instHMul.hMul (uHigh t) (abs (xHat (instHAdd.hAdd i 1) t j)))) →
                                                ((i : Nat) →
                                                    HighamBench.P16LowPrecisionMGSRestart l
                                                      (fun t => instHAdd.hAdd (uHigh t) (uLow t)) A Ainv b xExact
                                                      (xHat i) (xHat (instHAdd.hAdd i 1)) (residualHat i)
                                                      (correctionHat i) uLow polynomialFactor) →
                                                  (∀ (i : Nat),
                                                      HighamBench.p16FirstOrderLeAt l
                                                        (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                        (fun t => HighamBench.p16VecNorm (xHat i t)) fun t =>
                                                        HighamBench.p16VecNorm (xHat (instHAdd.hAdd i 1) t)) →
                                                    (∀ (i : Nat),
                                                        HighamBench.p16FirstOrderLeAt l
                                                          (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                          (fun t => HighamBench.p16VecNorm (xHat (instHAdd.hAdd i 1) t))
                                                          fun x => HighamBench.p16VecNorm xExact) →
                                                      (∀ (i : Nat),
                                                          HighamBench.p16FirstOrderLeAt l
                                                            (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                            (fun t =>
                                                              instHDiv.hDiv
                                                                (instHAdd.hAdd
                                                                  (HighamBench.p16VecNorm (residualError i t))
                                                                  (HighamBench.p16VecNorm
                                                                    (HighamBench.p16MatVec A (updateError i t))))
                                                                (instHAdd.hAdd (HighamBench.p16VecNorm b)
                                                                  (instHMul.hMul (HighamBench.p16FrobNorm A)
                                                                    (HighamBench.p16VecNorm
                                                                      (xHat (instHAdd.hAdd i 1) t)))))
                                                            fun t =>
                                                            instHMul.hMul
                                                              (HighamBench.p16PolynomialFactorValue polynomialFactor n
                                                                n)
                                                              (uHigh t)) →
                                                        (∀ (i : Nat),
                                                            HighamBench.p16FirstOrderLeAt l
                                                              (fun t => instHAdd.hAdd (uHigh t) (uLow t))
                                                              (fun t =>
                                                                instHDiv.hDiv (HighamBench.p16VecNorm (updateError i t))
                                                                  (HighamBench.p16VecNorm xExact))
                                                              fun t =>
                                                              instHMul.hMul
                                                                (instHMul.hMul
                                                                  (HighamBench.p16PolynomialFactorValue polynomialFactor
                                                                    n n)
                                                                  (uHigh t))
                                                                (HighamBench.p16ConditionNumberF A Ainv)) →
                                                          HighamBench.P16MixedPrecisionGMRESRun l
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
        (A Ainv : HighamBench.P16Matrix n) →
          (b xExact : HighamBench.P16Vector n) →
            (xHat residualHat correctionHat residualError updateError : Nat → ι → HighamBench.P16Vector n) →
              (uHigh uLow : ι → Real) →
                (polynomialFactor : HighamBench.P16PolynomialFactor) →
                  (b_nonzero :
                      @Ne.{1} (HighamBench.P16Vector n) b
                        (@OfNat.ofNat.{0} (HighamBench.P16Vector n) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (HighamBench.P16Vector n)
                            (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                              Real.instZero)))) →
                    (nonsingular : @HighamBench.p16IsNonsingular n A) →
                      (left_inverse_action :
                          ∀ (z : HighamBench.P16Vector n),
                            @Eq.{1} (HighamBench.P16Vector n)
                              (@HighamBench.p16MatVec n Ainv (@HighamBench.p16MatVec n A z)) z) →
                        (right_inverse_action :
                            ∀ (z : HighamBench.P16Vector n),
                              @Eq.{1} (HighamBench.P16Vector n)
                                (@HighamBench.p16MatVec n A (@HighamBench.p16MatVec n Ainv z)) z) →
                          (exact_solution : @Eq.{1} (HighamBench.P16Vector n) (@HighamBench.p16MatVec n A xExact) b) →
                            (uHigh_nonneg :
                                ∀ (t : ι),
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (uHigh t)) →
                              (uLow_nonneg :
                                  ∀ (t : ι),
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (uLow t)) →
                                (uHigh_le_uLow : ∀ (t : ι), @LE.le.{0} Real Real.instLE (uHigh t) (uLow t)) →
                                  (uHigh_tendsto_zero :
                                      @Filter.Tendsto.{u_1, 0} ι Real uHigh l
                                        (@nhds.{0} Real
                                          (@UniformSpace.toTopologicalSpace.{0} Real
                                            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                    (uLow_tendsto_zero :
                                        @Filter.Tendsto.{u_1, 0} ι Real uLow l
                                          (@nhds.{0} Real
                                            (@UniformSpace.toTopologicalSpace.{0} Real
                                              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                              (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                      (high_gamma_valid : ∀ (t : ι), HighamBench.GammaValid (uHigh t) n) →
                                        (residual_equation :
                                            ∀ (i : Nat) (t : ι),
                                              @Eq.{1} (HighamBench.P16Vector n) (residualHat i t)
                                                (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                  (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                  (@instHAdd.{0} (HighamBench.P16Vector n)
                                                    (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                      fun (i : Fin n) => Real.instAdd))
                                                  (@HighamBench.p16Residual n A b (xHat i t)) (residualError i t))) →
                                          (residual_error_bound :
                                              ∀ (i : Nat) (t : ι) (j : Fin n),
                                                @LE.le.{0} Real Real.instLE
                                                  (@abs.{0} Real Real.lattice Real.instAddGroup (residualError i t j))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (HighamBench.gamma (uHigh t) n)
                                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                      (@instHAdd.{0} Real Real.instAdd)
                                                      (@abs.{0} Real Real.lattice Real.instAddGroup (b j))
                                                      (@HighamBench.p16MatVec n
                                                        (fun (row col : Fin n) =>
                                                          @abs.{0} Real Real.lattice Real.instAddGroup (A row col))
                                                        (fun (col : Fin n) =>
                                                          @abs.{0} Real Real.lattice Real.instAddGroup (xHat i t col))
                                                        j)))) →
                                            (update_equation :
                                                ∀ (i : Nat) (t : ι),
                                                  @Eq.{1} (HighamBench.P16Vector n)
                                                    (xHat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                      t)
                                                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                      (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                      (@instHAdd.{0} (HighamBench.P16Vector n)
                                                        (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                          fun (i : Fin n) => Real.instAdd))
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                        (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                        (@instHAdd.{0} (HighamBench.P16Vector n)
                                                          (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                            fun (i : Fin n) => Real.instAdd))
                                                        (xHat i t) (correctionHat i t))
                                                      (updateError i t))) →
                                              (update_error_bound :
                                                  ∀ (i : Nat) (t : ι) (j : Fin n),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@abs.{0} Real Real.lattice Real.instAddGroup (updateError i t j))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) (uHigh t)
                                                        (@abs.{0} Real Real.lattice Real.instAddGroup
                                                          (xHat
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) i
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))
                                                            t j)))) →
                                                (restart :
                                                    (i : Nat) →
                                                      @HighamBench.P16LowPrecisionMGSRestart.{u_1} n ι l
                                                        (fun (t : ι) =>
                                                          @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                            (@instHAdd.{0} Real Real.instAdd) (uHigh t) (uLow t))
                                                        A Ainv b xExact (xHat i)
                                                        (xHat
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) i
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1)))))
                                                        (residualHat i) (correctionHat i) uLow polynomialFactor) →
                                                  (iterate_norm_current_next :
                                                      ∀ (i : Nat),
                                                        @HighamBench.p16FirstOrderLeAt.{u_1} ι l
                                                          (fun (t : ι) =>
                                                            @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                              (@instHAdd.{0} Real Real.instAdd) (uHigh t) (uLow t))
                                                          (fun (t : ι) => @HighamBench.p16VecNorm n (xHat i t))
                                                          fun (t : ι) =>
                                                          @HighamBench.p16VecNorm n
                                                            (xHat
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) i
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              t)) →
                                                    (iterate_norm_next_solution :
                                                        ∀ (i : Nat),
                                                          @HighamBench.p16FirstOrderLeAt.{u_1} ι l
                                                            (fun (t : ι) =>
                                                              @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                (@instHAdd.{0} Real Real.instAdd) (uHigh t) (uLow t))
                                                            (fun (t : ι) =>
                                                              @HighamBench.p16VecNorm n
                                                                (xHat
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) i
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))
                                                                  t))
                                                            fun (x : ι) => @HighamBench.p16VecNorm n xExact) →
                                                      (backward_high_roundoff_bound :
                                                          ∀ (i : Nat),
                                                            @HighamBench.p16FirstOrderLeAt.{u_1} ι l
                                                              (fun (t : ι) =>
                                                                @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                  (@instHAdd.{0} Real Real.instAdd) (uHigh t) (uLow t))
                                                              (fun (t : ι) =>
                                                                @HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                  (@instHDiv.{0} Real
                                                                    (@DivInvMonoid.toDiv.{0} Real
                                                                      Real.instDivInvMonoid))
                                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                    (@instHAdd.{0} Real Real.instAdd)
                                                                    (@HighamBench.p16VecNorm n (residualError i t))
                                                                    (@HighamBench.p16VecNorm n
                                                                      (@HighamBench.p16MatVec n A (updateError i t))))
                                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                    (@instHAdd.{0} Real Real.instAdd)
                                                                    (@HighamBench.p16VecNorm n b)
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul)
                                                                      (@HighamBench.p16FrobNorm n A)
                                                                      (@HighamBench.p16VecNorm n
                                                                        (xHat
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) i
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                              (instOfNatNat (nat_lit 1))))
                                                                          t)))))
                                                              fun (t : ι) =>
                                                              @HMul.hMul.{0, 0, 0} Real Real Real
                                                                (@instHMul.{0} Real Real.instMul)
                                                                (HighamBench.p16PolynomialFactorValue polynomialFactor n
                                                                  n)
                                                                (uHigh t)) →
                                                        (forward_high_roundoff_bound :
                                                            ∀ (i : Nat),
                                                              @HighamBench.p16FirstOrderLeAt.{u_1} ι l
                                                                (fun (t : ι) =>
                                                                  @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                    (@instHAdd.{0} Real Real.instAdd) (uHigh t)
                                                                    (uLow t))
                                                                (fun (t : ι) =>
                                                                  @HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                    (@instHDiv.{0} Real
                                                                      (@DivInvMonoid.toDiv.{0} Real
                                                                        Real.instDivInvMonoid))
                                                                    (@HighamBench.p16VecNorm n (updateError i t))
                                                                    (@HighamBench.p16VecNorm n xExact))
                                                                fun (t : ι) =>
                                                                @HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul)
                                                                    (HighamBench.p16PolynomialFactorValue
                                                                      polynomialFactor n n)
                                                                    (uHigh t))
                                                                  (@HighamBench.p16ConditionNumberF n A Ainv)) →
                                                          @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l
```

### D017: `HighamBench.P16MixedPrecisionGMRESRun.polynomialFactor`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `1007f4b6a0c6e4705c1a6856afa04909a8cc859086d0998eecd0b8b7a11e1e01`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → HighamBench.P16PolynomialFactor
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → HighamBench.P16PolynomialFactor
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.13
```

### D018: `HighamBench.P16MixedPrecisionGMRESRun.uHigh`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c918ae2d5722eb61527ca7f064fa91fff18127862bf1947e1f1ea4e3605cd3d8`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.11
```

### D019: `HighamBench.P16MixedPrecisionGMRESRun.uLow`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `050a7c54f7eb4705624e61e49e6219a91055717d6df8b41a725aab429fb1d485`

Type:

```lean
{n : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P16MixedPrecisionGMRESRun l → ι → Real
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} → {l : Filter.{u_1} ι} → (self : @HighamBench.P16MixedPrecisionGMRESRun.{u_1} n ι l) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun n ι l self => self.12
```

### D020: `HighamBench.P16Vector`

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

### D021: `HighamBench.p16ConditionNumberF`

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

### D022: `HighamBench.p16NormalizedResidual`

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

### D023: `HighamBench.p16PolynomialFactorValue`

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

### D024: `HighamBench.p16SecondOrderAt`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9f8f2149f6244d786fa2d0abae769fb5885e4da9a6f980dcd98dfdedc9dfea99`

Type:

```lean
{ι : Type u_1} → Filter ι → (ι → Real) → (ι → Real) → Prop
```

Fully explicit type:

```lean
{ι : Type u_1} → (l : Filter.{u_1} ι) → (scale remainder : ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} l scale remainder => Asymptotics.IsBigO l remainder fun t => instHPow.hPow (scale t) 2
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

### D026: `HighamBench.GammaValid`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `651ef903a8d9a3c8f539284f6c70325cebe6e199aad808cb56d9123f31e258c9`

Type:

```lean
Real → Nat → Prop
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u n => Real.instLT.lt (instHMul.hMul n.cast u) 1
```

### D027: `HighamBench.P16LowPrecisionMGSRestart`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `e45857733ce3798f3d60a8367e1ac10498ff41b2fa8efcd1445a0e775b8a30c9`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    Filter ι →
      (ι → Real) →
        HighamBench.P16Matrix n →
          HighamBench.P16Matrix n →
            HighamBench.P16Vector n →
              HighamBench.P16Vector n →
                (ι → HighamBench.P16Vector n) →
                  (ι → HighamBench.P16Vector n) →
                    (ι → HighamBench.P16Vector n) →
                      (ι → HighamBench.P16Vector n) → (ι → Real) → HighamBench.P16PolynomialFactor → Type u_1
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    (l : Filter.{u_1} ι) →
      (scale : ι → Real) →
        (A Ainv : HighamBench.P16Matrix n) →
          (b xExact : HighamBench.P16Vector n) →
            (xCurrent xNext residualHat correctionHat : ι → HighamBench.P16Vector n) →
              (uLow : ι → Real) → (poly : HighamBench.P16PolynomialFactor) → Type u_1
```

### D028: `HighamBench.P16PolynomialFactor`

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

### D029: `HighamBench.P16PolynomialFactor.coefficient`

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

### D030: `HighamBench.P16PolynomialFactor.degreeK`

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

### D031: `HighamBench.P16PolynomialFactor.degreeN`

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

### D032: `HighamBench.gamma`

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

### D033: `HighamBench.p16FrobNorm`

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

### D034: `HighamBench.p16IsNonsingular`

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

### D035: `HighamBench.p16MatVec`

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

### D036: `HighamBench.p16Residual`

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

### D037: `HighamBench.P16LowPrecisionMGSRestart.mk`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `afe19ef6b610bd6de95ce6e9366187dc63c2d4914b7abf30c63e852f0f1f3000`

Type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {scale : ι → Real} →
        {A Ainv : HighamBench.P16Matrix n} →
          {b xExact : HighamBench.P16Vector n} →
            {xCurrent xNext residualHat correctionHat : ι → HighamBench.P16Vector n} →
              {uLow : ι → Real} →
                {poly : HighamBench.P16PolynomialFactor} →
                  (keyDimension : Nat) →
                    instLTNat.lt 0 keyDimension →
                      instLENat.le keyDimension n →
                        (basis : ι → HighamBench.P16RectMatrix n keyDimension) →
                          (basisNext : ι → HighamBench.P16RectMatrix n (instHAdd.hAdd keyDimension 1)) →
                            (hessenberg : ι → HighamBench.P16RectMatrix (instHAdd.hAdd keyDimension 1) keyDimension) →
                              (arnoldiError : ι → HighamBench.P16RectMatrix n keyDimension) →
                                (∀ (t : ι),
                                    Eq (HighamBench.p16SquareRectMul A (basis t))
                                      (instHAdd.hAdd (HighamBench.p16RectMatMul (basisNext t) (hessenberg t))
                                        (arnoldiError t))) →
                                  (residualLow residualCastError : ι → HighamBench.P16Vector n) →
                                    (∀ (t : ι),
                                        Eq (residualLow t) (instHAdd.hAdd (residualHat t) (residualCastError t))) →
                                      (∀ (t : ι),
                                          Real.instLE.le (HighamBench.p16VecNorm (residualCastError t))
                                            (instHMul.hMul (uLow t) (HighamBench.p16VecNorm (residualHat t)))) →
                                        (arnoldiProduct arnoldiProductError :
                                            ι → HighamBench.P16RectMatrix n keyDimension) →
                                          (∀ (t : ι),
                                              Eq (arnoldiProduct t)
                                                (instHAdd.hAdd (HighamBench.p16SquareRectMul A (basis t))
                                                  (arnoldiProductError t))) →
                                            (epsilonC epsilonB epsilonLS epsilonX : ι → Real) →
                                              (∀ (t : ι),
                                                  Real.instLE.le (HighamBench.p16RectFrobNorm (arnoldiProductError t))
                                                    (instHMul.hMul (epsilonC t)
                                                      (HighamBench.p16RectFrobNorm
                                                        (HighamBench.p16SquareRectMul A (basis t))))) →
                                                (leastSquaresRhsError : ι → HighamBench.P16Vector n) →
                                                  (leastSquaresMatrixError :
                                                      ι → HighamBench.P16RectMatrix n keyDimension) →
                                                    (leastSquaresY : ι → HighamBench.P16Vector keyDimension) →
                                                      (∀ (t : ι),
                                                          HighamBench.p16IsLeastSquaresSolution
                                                            (instHAdd.hAdd (arnoldiProduct t)
                                                              (leastSquaresMatrixError t))
                                                            (instHAdd.hAdd (residualLow t) (leastSquaresRhsError t))
                                                            (leastSquaresY t)) →
                                                        (∀ (t : ι),
                                                            Real.instLE.le
                                                              (HighamBench.p16VecNorm (leastSquaresRhsError t))
                                                              (instHMul.hMul (epsilonLS t)
                                                                (HighamBench.p16VecNorm (residualLow t)))) →
                                                          (∀ (t : ι),
                                                              Real.instLE.le
                                                                (HighamBench.p16RectFrobNorm
                                                                  (leastSquaresMatrixError t))
                                                                (instHMul.hMul (epsilonLS t)
                                                                  (HighamBench.p16RectFrobNorm (arnoldiProduct t)))) →
                                                            (correctionFormationError : ι → HighamBench.P16Vector n) →
                                                              (∀ (t : ι),
                                                                  Eq (correctionHat t)
                                                                    (instHAdd.hAdd
                                                                      (HighamBench.p16RectMatVec (basis t)
                                                                        (leastSquaresY t))
                                                                      (correctionFormationError t))) →
                                                                (∀ (t : ι),
                                                                    Real.instLE.le
                                                                      (HighamBench.p16VecNorm
                                                                        (correctionFormationError t))
                                                                      (instHMul.hMul
                                                                        (instHMul.hMul (epsilonX t)
                                                                          (HighamBench.p16RectFrobNorm (basis t)))
                                                                        (HighamBench.p16VecNorm (leastSquaresY t)))) →
                                                                  (∀ (t : ι),
                                                                      And (Real.instLE.le 0 (epsilonC t))
                                                                        (And (Real.instLE.le 0 (epsilonB t))
                                                                          (And (Real.instLE.le 0 (epsilonLS t))
                                                                            (Real.instLE.le 0 (epsilonX t))))) →
                                                                    And (Filter.Tendsto epsilonC l (nhds 0))
                                                                        (And (Filter.Tendsto epsilonB l (nhds 0))
                                                                          (And (Filter.Tendsto epsilonLS l (nhds 0))
                                                                            (Filter.Tendsto epsilonX l (nhds 0)))) →
                                                                      (basisLowerGain imageLowerGain : ι → Real) →
                                                                        (∀ (t : ι),
                                                                            HighamBench.p16MinGainAtLeast (basis t)
                                                                              (basisLowerGain t)) →
                                                                          (∀ (t : ι),
                                                                              HighamBench.p16MinGainAtLeast
                                                                                (HighamBench.p16SquareRectMul A
                                                                                  (basis t))
                                                                                (imageLowerGain t)) →
                                                                            (∀ (t : ι),
                                                                                Real.instLT.lt
                                                                                  (instHMul.hMul (epsilonX t)
                                                                                    (HighamBench.p16RectFrobNorm
                                                                                      (basis t)))
                                                                                  (basisLowerGain t)) →
                                                                              (instLTNat.lt keyDimension n →
                                                                                  ∀ (t : ι) (phi : Real),
                                                                                    Real.instLT.lt 0 phi →
                                                                                      HighamBench.p16NearRankDeficient
                                                                                        (HighamBench.p16Augment
                                                                                          (residualLow t) phi
                                                                                          (arnoldiProduct t))
                                                                                        (instHMul.hMul
                                                                                          (instHMul.hMul
                                                                                            (HighamBench.p16PolynomialFactorValue
                                                                                              poly n keyDimension)
                                                                                            (instHAdd.hAdd
                                                                                              (instHAdd.hAdd
                                                                                                (epsilonC t)
                                                                                                (epsilonB t))
                                                                                              (epsilonLS t)))
                                                                                          (HighamBench.p16RectFrobNorm
                                                                                            (HighamBench.p16Augment
                                                                                              (residualLow t) phi
                                                                                              (arnoldiProduct t))))) →
                                                                                (∀ (t : ι),
                                                                                    Real.instLT.lt
                                                                                      (instHMul.hMul
                                                                                        (instHAdd.hAdd
                                                                                          (instHAdd.hAdd (epsilonC t)
                                                                                            (epsilonB t))
                                                                                          (epsilonLS t))
                                                                                        (HighamBench.p16RectFrobNorm
                                                                                          (arnoldiProduct t)))
                                                                                      (imageLowerGain t)) →
                                                                                  (localFactor : Real) →
                                                                                    Real.instLE.le 0 localFactor →
                                                                                      Real.instLE.le localFactor
                                                                                          (HighamBench.p16PolynomialFactorValue
                                                                                            poly n keyDimension) →
                                                                                        Real.instLE.le
                                                                                            (HighamBench.p16PolynomialFactorValue
                                                                                              poly n keyDimension)
                                                                                            (HighamBench.p16PolynomialFactorValue
                                                                                              poly n n) →
                                                                                          (backwardFactor
                                                                                              forwardFactor :
                                                                                              ι → Real) →
                                                                                            (∀ (t : ι),
                                                                                                And
                                                                                                  (Real.instLE.le 0
                                                                                                    (backwardFactor t))
                                                                                                  (Real.instLE.le 0
                                                                                                    (forwardFactor
                                                                                                      t))) →
                                                                                              (∀ (t : ι),
                                                                                                  Real.instLE.le
                                                                                                    (backwardFactor t)
                                                                                                    (instHMul.hMul
                                                                                                      (instHMul.hMul
                                                                                                        localFactor
                                                                                                        (uLow t))
                                                                                                      (HighamBench.p16ConditionNumberF
                                                                                                        A Ainv))) →
                                                                                                (∀ (t : ι),
                                                                                                    Real.instLE.le
                                                                                                      (forwardFactor t)
                                                                                                      (instHMul.hMul
                                                                                                        (instHMul.hMul
                                                                                                          localFactor
                                                                                                          (uLow t))
                                                                                                        (HighamBench.p16ConditionNumberF
                                                                                                          A Ainv))) →
                                                                                                  (HighamBench.p16FirstOrderLeAt
                                                                                                      l scale ⋯ fun t =>
                                                                                                      instHMul.hMul
                                                                                                        (backwardFactor
                                                                                                          t)
                                                                                                        (HighamBench.p16BackwardError
                                                                                                          A b
                                                                                                          (xCurrent
                                                                                                            t))) →
                                                                                                    ⋯ → ⋯
```

Fully explicit type:

```lean
{n : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {scale : ι → Real} →
        {A Ainv : HighamBench.P16Matrix n} →
          {b xExact : HighamBench.P16Vector n} →
            {xCurrent xNext residualHat correctionHat : ι → HighamBench.P16Vector n} →
              {uLow : ι → Real} →
                {poly : HighamBench.P16PolynomialFactor} →
                  (keyDimension : Nat) →
                    (keyDimension_pos :
                        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          keyDimension) →
                      (keyDimension_le : @LE.le.{0} Nat instLENat keyDimension n) →
                        (basis : ι → HighamBench.P16RectMatrix n keyDimension) →
                          (basisNext :
                              ι →
                                HighamBench.P16RectMatrix n
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            (hessenberg :
                                ι →
                                  HighamBench.P16RectMatrix
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keyDimension
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    keyDimension) →
                              (arnoldiError : ι → HighamBench.P16RectMatrix n keyDimension) →
                                (arnoldi_relation :
                                    ∀ (t : ι),
                                      @Eq.{1} (HighamBench.P16RectMatrix n keyDimension)
                                        (@HighamBench.p16SquareRectMul n keyDimension A (basis t))
                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16RectMatrix n keyDimension)
                                          (HighamBench.P16RectMatrix n keyDimension)
                                          (HighamBench.P16RectMatrix n keyDimension)
                                          (@instHAdd.{0} (HighamBench.P16RectMatrix n keyDimension)
                                            (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real Real.instAdd))
                                          (@HighamBench.p16RectMatMul n
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              keyDimension
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            keyDimension (basisNext t) (hessenberg t))
                                          (arnoldiError t))) →
                                  (residualLow residualCastError : ι → HighamBench.P16Vector n) →
                                    (residual_cast_equation :
                                        ∀ (t : ι),
                                          @Eq.{1} (HighamBench.P16Vector n) (residualLow t)
                                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                              (HighamBench.P16Vector n)
                                              (@instHAdd.{0} (HighamBench.P16Vector n)
                                                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                  Real.instAdd))
                                              (residualHat t) (residualCastError t))) →
                                      (residual_cast_bound :
                                          ∀ (t : ι),
                                            @LE.le.{0} Real Real.instLE
                                              (@HighamBench.p16VecNorm n (residualCastError t))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (uLow t) (@HighamBench.p16VecNorm n (residualHat t)))) →
                                        (arnoldiProduct arnoldiProductError :
                                            ι → HighamBench.P16RectMatrix n keyDimension) →
                                          (arnoldi_product_equation :
                                              ∀ (t : ι),
                                                @Eq.{1} (HighamBench.P16RectMatrix n keyDimension) (arnoldiProduct t)
                                                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16RectMatrix n keyDimension)
                                                    (HighamBench.P16RectMatrix n keyDimension)
                                                    (HighamBench.P16RectMatrix n keyDimension)
                                                    (@instHAdd.{0} (HighamBench.P16RectMatrix n keyDimension)
                                                      (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real
                                                        Real.instAdd))
                                                    (@HighamBench.p16SquareRectMul n keyDimension A (basis t))
                                                    (arnoldiProductError t))) →
                                            (epsilonC epsilonB epsilonLS epsilonX : ι → Real) →
                                              (arnoldi_product_bound :
                                                  ∀ (t : ι),
                                                    @LE.le.{0} Real Real.instLE
                                                      (@HighamBench.p16RectFrobNorm n keyDimension
                                                        (arnoldiProductError t))
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) (epsilonC t)
                                                        (@HighamBench.p16RectFrobNorm n keyDimension
                                                          (@HighamBench.p16SquareRectMul n keyDimension A
                                                            (basis t))))) →
                                                (leastSquaresRhsError : ι → HighamBench.P16Vector n) →
                                                  (leastSquaresMatrixError :
                                                      ι → HighamBench.P16RectMatrix n keyDimension) →
                                                    (leastSquaresY : ι → HighamBench.P16Vector keyDimension) →
                                                      (least_squares_solution :
                                                          ∀ (t : ι),
                                                            @HighamBench.p16IsLeastSquaresSolution n keyDimension
                                                              (@HAdd.hAdd.{0, 0, 0}
                                                                (HighamBench.P16RectMatrix n keyDimension)
                                                                (HighamBench.P16RectMatrix n keyDimension)
                                                                (HighamBench.P16RectMatrix n keyDimension)
                                                                (@instHAdd.{0}
                                                                  (HighamBench.P16RectMatrix n keyDimension)
                                                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin keyDimension) Real
                                                                    Real.instAdd))
                                                                (arnoldiProduct t) (leastSquaresMatrixError t))
                                                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                                (HighamBench.P16Vector n) (HighamBench.P16Vector n)
                                                                (@instHAdd.{0} (HighamBench.P16Vector n)
                                                                  (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                                    fun (i : Fin n) => Real.instAdd))
                                                                (residualLow t) (leastSquaresRhsError t))
                                                              (leastSquaresY t)) →
                                                        (least_squares_rhs_bound :
                                                            ∀ (t : ι),
                                                              @LE.le.{0} Real Real.instLE
                                                                (@HighamBench.p16VecNorm n (leastSquaresRhsError t))
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul) (epsilonLS t)
                                                                  (@HighamBench.p16VecNorm n (residualLow t)))) →
                                                          (least_squares_matrix_bound :
                                                              ∀ (t : ι),
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@HighamBench.p16RectFrobNorm n keyDimension
                                                                    (leastSquaresMatrixError t))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul) (epsilonLS t)
                                                                    (@HighamBench.p16RectFrobNorm n keyDimension
                                                                      (arnoldiProduct t)))) →
                                                            (correctionFormationError : ι → HighamBench.P16Vector n) →
                                                              (correction_formation_equation :
                                                                  ∀ (t : ι),
                                                                    @Eq.{1} (HighamBench.P16Vector n) (correctionHat t)
                                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P16Vector n)
                                                                        (HighamBench.P16Vector n)
                                                                        (HighamBench.P16Vector n)
                                                                        (@instHAdd.{0} (HighamBench.P16Vector n)
                                                                          (@Pi.instAdd.{0, 0} (Fin n)
                                                                            (fun (a : Fin n) => Real) fun (i : Fin n) =>
                                                                            Real.instAdd))
                                                                        (@HighamBench.p16RectMatVec n keyDimension
                                                                          (basis t) (leastSquaresY t))
                                                                        (correctionFormationError t))) →
                                                                (correction_formation_bound :
                                                                    ∀ (t : ι),
                                                                      @LE.le.{0} Real Real.instLE
                                                                        (@HighamBench.p16VecNorm n
                                                                          (correctionFormationError t))
                                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                          (@instHMul.{0} Real Real.instMul)
                                                                          (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                            (@instHMul.{0} Real Real.instMul)
                                                                            (epsilonX t)
                                                                            (@HighamBench.p16RectFrobNorm n keyDimension
                                                                              (basis t)))
                                                                          (@HighamBench.p16VecNorm keyDimension
                                                                            (leastSquaresY t)))) →
                                                                  (accuracy_nonneg :
                                                                      ∀ (t : ι),
                                                                        And
                                                                          (@LE.le.{0} Real Real.instLE
                                                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                              (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                            (epsilonC t))
                                                                          (And
                                                                            (@LE.le.{0} Real Real.instLE
                                                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                              (epsilonB t))
                                                                            (And
                                                                              (@LE.le.{0} Real Real.instLE
                                                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                  (@Zero.toOfNat0.{0} Real
                                                                                    Real.instZero))
                                                                                (epsilonLS t))
                                                                              (@LE.le.{0} Real Real.instLE
                                                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                  (@Zero.toOfNat0.{0} Real
                                                                                    Real.instZero))
                                                                                (epsilonX t))))) →
                                                                    (accuracy_tendsto_zero :
                                                                        And
                                                                          (@Filter.Tendsto.{u_1, 0} ι Real epsilonC l
                                                                            (@nhds.{0} Real
                                                                              (@UniformSpace.toTopologicalSpace.{0} Real
                                                                                (@PseudoMetricSpace.toUniformSpace.{0}
                                                                                  Real Real.pseudoMetricSpace))
                                                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                (@Zero.toOfNat0.{0} Real
                                                                                  Real.instZero))))
                                                                          (And
                                                                            (@Filter.Tendsto.{u_1, 0} ι Real epsilonB l
                                                                              (@nhds.{0} Real
                                                                                (@UniformSpace.toTopologicalSpace.{0}
                                                                                  Real
                                                                                  (@PseudoMetricSpace.toUniformSpace.{0}
                                                                                    Real Real.pseudoMetricSpace))
                                                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                  (@Zero.toOfNat0.{0} Real
                                                                                    Real.instZero))))
                                                                            (And
                                                                              (@Filter.Tendsto.{u_1, 0} ι Real epsilonLS
                                                                                l
                                                                                (@nhds.{0} Real
                                                                                  (@UniformSpace.toTopologicalSpace.{0}
                                                                                    Real
                                                                                    (@PseudoMetricSpace.toUniformSpace.{0}
                                                                                      Real Real.pseudoMetricSpace))
                                                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                    (@Zero.toOfNat0.{0} Real
                                                                                      Real.instZero))))
                                                                              (@Filter.Tendsto.{u_1, 0} ι Real epsilonX
                                                                                l
                                                                                (@nhds.{0} Real
                                                                                  (@UniformSpace.toTopologicalSpace.{0}
                                                                                    Real
                                                                                    (@PseudoMetricSpace.toUniformSpace.{0}
                                                                                      Real Real.pseudoMetricSpace))
                                                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                                    (@Zero.toOfNat0.{0} Real
                                                                                      Real.instZero))))))) →
                                                                      (basisLowerGain imageLowerGain : ι → Real) →
                                                                        (basis_gain :
                                                                            ∀ (t : ι),
                                                                              @HighamBench.p16MinGainAtLeast n
                                                                                keyDimension (basis t)
                                                                                (basisLowerGain t)) →
                                                                          (image_gain :
                                                                              ∀ (t : ι),
                                                                                @HighamBench.p16MinGainAtLeast n
                                                                                  keyDimension
                                                                                  (@HighamBench.p16SquareRectMul n
                                                                                    keyDimension A (basis t))
                                                                                  (imageLowerGain t)) →
                                                                            (basis_not_numerically_rank_deficient :
                                                                                ∀ (t : ι),
                                                                                  @LT.lt.{0} Real Real.instLT
                                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                      (@instHMul.{0} Real Real.instMul)
                                                                                      (epsilonX t)
                                                                                      (@HighamBench.p16RectFrobNorm n
                                                                                        keyDimension (basis t)))
                                                                                    (basisLowerGain t)) →
                                                                              (key_near_dependence :
                                                                                  @LT.lt.{0} Nat instLTNat keyDimension
                                                                                      n →
                                                                                    ∀ (t : ι) (phi : Real),
                                                                                      @LT.lt.{0} Real Real.instLT
                                                                                          (@OfNat.ofNat.{0} Real
                                                                                            (nat_lit 0)
                                                                                            (@Zero.toOfNat0.{0} Real
                                                                                              Real.instZero))
                                                                                          phi →
                                                                                        @HighamBench.p16NearRankDeficient
                                                                                          n
                                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat
                                                                                            Nat
                                                                                            (@instHAdd.{0} Nat
                                                                                              instAddNat)
                                                                                            keyDimension
                                                                                            (@OfNat.ofNat.{0} Nat
                                                                                              (nat_lit 1)
                                                                                              (instOfNatNat
                                                                                                (nat_lit 1))))
                                                                                          (@HighamBench.p16Augment n
                                                                                            keyDimension (residualLow t)
                                                                                            phi (arnoldiProduct t))
                                                                                          (@HMul.hMul.{0, 0, 0} Real
                                                                                            Real Real
                                                                                            (@instHMul.{0} Real
                                                                                              Real.instMul)
                                                                                            (@HMul.hMul.{0, 0, 0} Real
                                                                                              Real Real
                                                                                              (@instHMul.{0} Real
                                                                                                Real.instMul)
                                                                                              (HighamBench.p16PolynomialFactorValue
                                                                                                poly n keyDimension)
                                                                                              (@HAdd.hAdd.{0, 0, 0} Real
                                                                                                Real Real
                                                                                                (@instHAdd.{0} Real
                                                                                                  Real.instAdd)
                                                                                                (@HAdd.hAdd.{0, 0, 0}
                                                                                                  Real Real Real
                                                                                                  (@instHAdd.{0} Real
                                                                                                    Real.instAdd)
                                                                                                  (epsilonC t)
                                                                                                  (epsilonB t))
                                                                                                (epsilonLS t)))
                                                                                            (@HighamBench.p16RectFrobNorm
                                                                                              n
                                                                                              (@HAdd.hAdd.{0, 0, 0} Nat
                                                                                                Nat Nat
                                                                                                (@instHAdd.{0} Nat
                                                                                                  instAddNat)
                                                                                                keyDimension
                                                                                                (@OfNat.ofNat.{0} Nat
                                                                                                  (nat_lit 1)
                                                                                                  (instOfNatNat
                                                                                                    (nat_lit 1))))
                                                                                              (@HighamBench.p16Augment n
                                                                                                keyDimension
                                                                                                (residualLow t) phi
                                                                                                (arnoldiProduct t))))) →
                                                                                (key_image_full_rank :
                                                                                    ∀ (t : ι),
                                                                                      @LT.lt.{0} Real Real.instLT
                                                                                        (@HMul.hMul.{0, 0, 0} Real Real
                                                                                          Real
                                                                                          (@instHMul.{0} Real
                                                                                            Real.instMul)
                                                                                          (@HAdd.hAdd.{0, 0, 0} Real
                                                                                            Real Real
                                                                                            (@instHAdd.{0} Real
                                                                                              Real.instAdd)
                                                                                            (@HAdd.hAdd.{0, 0, 0} Real
                                                                                              Real Real
                                                                                              (@instHAdd.{0} Real
                                                                                                Real.instAdd)
                                                                                              (epsilonC t) (epsilonB t))
                                                                                            (epsilonLS t))
                                                                                          (@HighamBench.p16RectFrobNorm
                                                                                            n keyDimension
                                                                                            (arnoldiProduct t)))
                                                                                        (imageLowerGain t)) →
                                                                                  (localFactor : Real) →
                                                                                    (localFactor_nonneg :
                                                                                        @LE.le.{0} Real Real.instLE
                                                                                          (@OfNat.ofNat.{0} Real
                                                                                            (nat_lit 0)
                                                                                            (@Zero.toOfNat0.{0} Real
                                                                                              Real.instZero))
                                                                                          localFactor) →
                                                                                      (localFactor_polynomial_bound :
                                                                                          @LE.le.{0} Real Real.instLE
                                                                                            localFactor
                                                                                            (HighamBench.p16PolynomialFactorValue
                                                                                              poly n keyDimension)) →
                                                                                        (localFactor_uniform_bound :
                                                                                            @LE.le.{0} Real Real.instLE
                                                                                              (HighamBench.p16PolynomialFactorValue
                                                                                                poly n keyDimension)
                                                                                              (HighamBench.p16PolynomialFactorValue
                                                                                                poly n n)) →
                                                                                          (backwardFactor
                                                                                              forwardFactor :
                                                                                              ι → Real) →
                                                                                            (factors_nonneg :
                                                                                                ∀ (t : ι),
                                                                                                  And
                                                                                                    (@LE.le.{0} Real
                                                                                                      Real.instLE
                                                                                                      (@OfNat.ofNat.{0}
                                                                                                        Real (nat_lit 0)
                                                                                                        (@Zero.toOfNat0.{0}
                                                                                                          Real
                                                                                                          Real.instZero))
                                                                                                      (backwardFactor
                                                                                                        t))
                                                                                                    (@LE.le.{0} Real
                                                                                                      Real.instLE
                                                                                                      (@OfNat.ofNat.{0}
                                                                                                        Real (nat_lit 0)
                                                                                                        (@Zero.toOfNat0.{0}
                                                                                                          Real
                                                                                                          Real.instZero))
                                                                                                      (forwardFactor
                                                                                                        t))) →
                                                                                              (backward_factor_bound :
                                                                                                  ∀ (t : ι),
                                                                                                    @LE.le.{0} Real
                                                                                                      Real.instLE
                                                                                                      (backwardFactor t)
                                                                                                      (@HMul.hMul.{0, 0,
                                                                                                            0}
                                                                                                        Real Real Real
                                                                                                        (@instHMul.{0}
                                                                                                          Real
                                                                                                          Real.instMul)
                                                                                                        (@HMul.hMul.{0,
                                                                                                              0, 0}
                                                                                                          Real Real Real
                                                                                                          (@instHMul.{0}
                                                                                                            Real
                                                                                                            Real.instMul)
                                                                                                          localFactor
                                                                                                          (uLow t))
                                                                                                        (@HighamBench.p16ConditionNumberF
                                                                                                          n A Ainv))) →
                                                                                                (forward_factor_bound :
                                                                                                    ∀ (t : ι),
                                                                                                      @LE.le.{0} Real
                                                                                                        Real.instLE
                                                                                                        (forwardFactor
                                                                                                          t)
                                                                                                        (@HMul.hMul.{0,
                                                                                                              0, 0}
                                                                                                          Real Real Real
                                                                                                          (@instHMul.{0}
                                                                                                            Real
                                                                                                            Real.instMul)
                                                                                                          (@HMul.hMul.{0,
                                                                                                                0, 0}
                                                                                                            Real Real
                                                                                                            Real
                                                                                                            (@instHMul.{0}
                                                                                                              Real
                                                                                                              Real.instMul)
                                                                                                            localFactor
                                                                                                            (uLow t))
                                                                                                          (@HighamBench.p16ConditionNumberF
                                                                                                            n A
                                                                                                            Ainv))) →
                                                                                                  (backward_correction_bound :
                                                                                                      @HighamBench.p16FirstOrderLeAt.{u_1}
                                                                                                        ι l scale
                                                                                                        (fun (t : ι) =>
                                                                                                          @HDiv.hDiv.{0,
                                                                                                                0, 0}
                                                                                                            Real Real
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
                                                                                                                (residualHat
                                                                                                                  t)
                                                                                                                (@HighamBench.p16MatVec
                                                                                                                  n A
                                                                                                                  (correctionHat
                                                                                                                    t))))
                                                                                                            (@HAdd.hAdd.{0,
                                                                                                                  0, 0}
                                                                                                              Real Real
                                                                                                              Real
                                                                                                              (@instHAdd.{0}
                                                                                                                Real
                                                                                                                Real.instAdd)
                                                                                                              (@HighamBench.p16VecNorm
                                                                                                                n b)
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
                                                                                                                  n A)
                                                                                                                (@HighamBench.p16VecNorm
                                                                                                                  n
                                                                                                                  (xNext
                                                                                                                    t)))))
                                                                                                        fun (t : ι) =>
                                                                                                        @HMul.hMul.{0,
                                                                                                              0, 0}
                                                                                                          Real Real Real
                                                                                                          (@instHMul.{0}
                                                                                                            Real
                                                                                                            Real.instMul)
                                                                                                          (backwardFactor
                                                                                                            t)
                                                                                                          (@HighamBench.p16BackwardError
                                                                                                            n A b
                                                                                                            (xCurrent
                                                                                                              t))) →
                                                                                                    (forward_correction_bound :
                                                                                                        @HighamBench.p16FirstOrderLeAt.{u_1}
                                                                                                          ι l scale
                                                                                                          (fun
                                                                                                              (t : ι) =>
                                                                                                            @HDiv.hDiv.{0,
                                                                                                                  0, 0}
                                                                                                              Real Real
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
                                                                                                                    (xCurrent
                                                                                                                      t)
                                                                                                                    (correctionHat
                                                                                                                      t))
                                                                                                                  xExact))
                                                                                                              (@HighamBench.p16VecNorm
                                                                                                                n
                                                                                                                xExact))
                                                                                                          fun (t : ι) =>
                                                                                                          @HMul.hMul.{0,
                                                                                                                0, 0}
                                                                                                            Real Real
                                                                                                            Real
                                                                                                            (@instHMul.{0}
                                                                                                              Real
                                                                                                              Real.instMul)
                                                                                                            (forwardFactor
                                                                                                              t)
                                                                                                            (@HighamBench.p16ForwardError
                                                                                                              n xExact
                                                                                                              (xCurrent
                                                                                                                t))) →
                                                                                                      @HighamBench.P16LowPrecisionMGSRestart.{u_1}
                                                                                                        n ι l scale A
                                                                                                        Ainv b xExact
                                                                                                        xCurrent xNext
                                                                                                        residualHat
                                                                                                        correctionHat
                                                                                                        uLow poly
```

### D038: `HighamBench.P16PolynomialFactor.mk`

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

### D039: `HighamBench.P16RectMatrix`

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

### D040: `HighamBench.p16Augment`

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

### D045: `HighamBench.p16RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `4c41f6ed6f135d516ff29af2935748dc7ecc22eba1d40003bd16ecd29aa82ef9`

Type:

```lean
{m k q : Nat} → HighamBench.P16RectMatrix m k → HighamBench.P16RectMatrix k q → HighamBench.P16RectMatrix m q
```

Fully explicit type:

```lean
{m k q : Nat} →
  (A : HighamBench.P16RectMatrix m k) → (B : HighamBench.P16RectMatrix k q) → HighamBench.P16RectMatrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m k q} A B i j => Finset.univ.sum fun r => instHMul.hMul (A i r) (B r j)
```

### D046: `HighamBench.p16RectMatVec`

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

### D047: `HighamBench.p16SquareRectMul`

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

### D049: `Filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f178b01470c6b39d870c442162d6d76a8f2124db69fab7f84fe3f0f559dd4616`

Type:

```lean
Type u_1 → Type u_1
```

Fully explicit type:

```lean
(α : Type u_1) → Type u_1
```

### D050: `Filter.NeBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b1a9231cff02beea54a4a940464dcfebb9366c023dc4486941e5650f09abbe2c`

Type:

```lean
{α : Type u_1} → Filter α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → (f : Filter.{u_1} α) → Prop
```

### D051: `HAdd.hAdd`

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

### D052: `HMul.hMul`

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

### D053: `Nat`

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

### D054: `OfNat.ofNat`

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

### D057: `Real.instMul`

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

### D058: `instAddNat`

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

### D059: `instHAdd`

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

### D060: `instHMul`

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

### D061: `instOfNatNat`

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

### D062: `DivInvMonoid.toDiv`

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

### D063: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D064: `Filter.Eventually`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `48c8fc03616b0f899835653f1d062e3de4f566255a80b15231ebdedcb0a5c4c4`

Type:

```lean
{α : Type u_1} → (α → Prop) → Filter α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → (p : α → Prop) → (f : Filter.{u_1} α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} p f => Filter.instMembership.mem f (setOf fun x => p x)
```

### D065: `Filter.Tendsto`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Filter.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `7e5f54349644c32198960083c0e0eb6c033c80a8656d02a78b3eae9a4f5131f2`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → Filter α → Filter β → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → (f : α → β) → (l₁ : Filter.{u_1} α) → (l₂ : Filter.{u_2} β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f l₁ l₂ => Filter.instPartialOrder.le (Filter.map f l₁) l₂
```

### D066: `Fin`

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

### D067: `HDiv.hDiv`

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

### D068: `HSub.hSub`

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

### D069: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D070: `LT.lt`

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

### D071: `One.toOfNat1`

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

### D072: `Pi.instSub`

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

### D073: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : PseudoMetricSpace.{u} α] → UniformSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D074: `Real.instAddGroup`

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

### D075: `Real.instDivInvMonoid`

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

### D076: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D077: `Real.instLT`

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

### D078: `Real.instOne`

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

### D079: `Real.instSub`

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

### D080: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D081: `Real.lattice`

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

### D082: `Real.pseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `9c0d1d56a04dd3ae3fce36b5fb3c2f4fe632c2bdaed84b5667c1a60a03491a3e`

Type:

```lean
PseudoMetricSpace Real
```

Fully explicit type:

```lean
PseudoMetricSpace.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ dist := fun x y => abs (instHSub.hSub x y), dist_self := Real.pseudoMetricSpace._proof_1, dist_comm := ⋯,
  dist_triangle := ⋯, edist_dist := Real.pseudoMetricSpace._proof_2, uniformity_dist := Real.pseudoMetricSpace._proof_3,
  cobounded_sets := Real.pseudoMetricSpace._proof_4 }
```

### D083: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : UniformSpace.{u} α] → TopologicalSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D084: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D085: `abs`

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

### D086: `instHDiv`

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

### D087: `instHSub`

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

### D088: `nhds`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8eb445823f4b15a765f7e0cd634f73196d36b4f09054d2aef43a69d3138c6ce8`

Type:

```lean
{X : Type u_3} → [TopologicalSpace X] → X → Filter X
```

Fully explicit type:

```lean
{X : Type u_3} → [TopologicalSpace.{u_3} X] → (x : X) → Filter.{u_3} X
```

Definition body (one-level semantic boundary):

```lean
wrapped✝.1
```

### D089: `Asymptotics.IsBigO`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Asymptotics.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `06a15067a593fd57b03eac5fd3b1be5d0a4500012f1c2bd1c892def6eda93919`

Type:

```lean
{α : Type u_18} → {E : Type u_19} → {F : Type u_20} → [Norm E] → [Norm F] → Filter α → (α → E) → (α → F) → Prop
```

Fully explicit type:

```lean
{α : Type u_18} →
  {E : Type u_19} →
    {F : Type u_20} → [Norm.{u_19} E] → [Norm.{u_20} F] → (l : Filter.{u_18} α) → (f : α → E) → (g : α → F) → Prop
```

Definition body (one-level semantic boundary):

```lean
Asymptotics.wrapped✝.1
```

### D090: `Eq`

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

### D091: `Fin.fintype`

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

### D092: `Fin.val`

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

### D093: `Finset.sum`

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

### D094: `Finset.univ`

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

### D095: `HPow.hPow`

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

### D096: `Matrix`

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

### D097: `Monoid.toNatPow`

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

### D098: `Nat.cast`

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

### D099: `Ne`

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

### D100: `Pi.instAdd`

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

### D101: `Pi.instZero`

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

### D102: `Real.instAddCommMonoid`

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

### D103: `Real.instMonoid`

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

### D104: `Real.instNatCast`

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

### D105: `Real.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Real`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e6d33c73e5cb8fae7d8c501ead6aad9e275f7969a4d8b80f94b9f3b5001bfe3a`

Type:

```lean
Norm Real
```

Fully explicit type:

```lean
Norm.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun r => abs r }
```

### D106: `Real.sqrt`

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

### D107: `instHPow`

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

### D108: `instLTNat`

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

### D109: `Function.Bijective`

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

### D110: `Matrix.frobeniusNormedRing`

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

### D111: `Norm.norm`

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

### D112: `NormedRing.toNorm`

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

### D113: `Real.instRCLike`

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

### D114: `instDecidableEqFin`

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

### D115: `Matrix.add`

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

### D116: `instLENat`

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

### D117: `Fin.cases`

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

### D118: `Matrix.frobeniusNormedAddCommGroup`

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

### D119: `NormedAddCommGroup.toNorm`

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

### D120: `Real.normedAddCommGroup`

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

### `HighamBench.P16Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P16Definitions.lean`
SHA-256: `d4ea17de614c48b1916c5ffba10daf092bf258761c0850111aa6c560eff72196`

```lean
import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P16 definitions

Paper-scoped finite-dimensional notation for the modular backward-error
analysis of GMRES and restarted GMRES.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P16 model. -/
abbrev P16Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite real vector in the P16 model. -/
abbrev P16Vector (n : ℕ) := Fin n → ℝ

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p16MatVec {n : ℕ} (A : P16Matrix n)
    (x : P16Vector n) : P16Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Frobenius norm used in the paper's normwise backward error. -/
noncomputable def p16FrobNorm {n : ℕ} (A : P16Matrix n) : ℝ :=
  ‖A‖

/-- Euclidean vector norm. -/
noncomputable def p16VecNorm {n : ℕ} (x : P16Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Exact residual `b - A x`. -/
noncomputable def p16Residual {n : ℕ} (A : P16Matrix n)
    (b x : P16Vector n) : P16Vector n :=
  b - p16MatVec A x

/-- A square matrix is nonsingular when its exact matrix-vector action is a
bijection. -/
def p16IsNonsingular {n : ℕ} (A : P16Matrix n) : Prop :=
  Function.Bijective (p16MatVec A)

/-- The shared relative perturbation condition in the paper's normwise
backward-error definition. -/
def p16NormwiseBackwardErrorAdmissible {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) (epsilon : ℝ) : Prop :=
  ∃ deltaA : P16Matrix n, ∃ deltaB : P16Vector n,
    p16MatVec (A + deltaA) xHat = b + deltaB ∧
      p16FrobNorm deltaA ≤ epsilon * p16FrobNorm A ∧
      p16VecNorm deltaB ≤ epsilon * p16VecNorm b

/-- The normalized residual on the right-hand side of the paper's exact
normwise backward-error formula. -/
noncomputable def p16NormalizedResidual {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n) : ℝ :=
  p16VecNorm (p16Residual A b xHat) /
    (p16FrobNorm A * p16VecNorm xHat + p16VecNorm b)

/-- A scalar remainder that is second order in `scale` along `l`. Dimensions
and the fixed refinement iteration are outside the limit, so the hidden Big-O
constant may depend on them exactly as in the paper's convention. -/
def p16SecondOrderAt {ι : Type*} (l : Filter ι) (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t ↦ scale t ^ 2

/-- A precise interpretation of the paper's `≲`: the inequality holds after
adding an otherwise unspecified second-order remainder. -/
def p16FirstOrderLeAt {ι : Type*} (l : Filter ι) (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p16SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- One computed generic iterative-refinement step in the backward-error
clause of Lemma 4.2. It records exactly the normwise operation models (4.1),
(4.2), and (4.14), together with the first-order iterate comparison used in
the proof of (4.15). -/
structure P16Lemma42BackwardStep {n : ℕ} {ι : Type*}
    (l : Filter ι) (scale : ι → ℝ)
    (A : P16Matrix n) (b : P16Vector n) (_iteration : ℕ) where
  xHat : ι → P16Vector n
  correctionHat : ι → P16Vector n
  xHatNext : ι → P16Vector n
  residualHat : ι → P16Vector n
  deltaR : ι → P16Vector n
  deltaX : ι → P16Vector n
  epsilonR : ι → ℝ
  epsilonU : ι → ℝ
  w : ι → ℝ
  omega : ι → ℝ
  residual_equation : ∀ t,
    residualHat t = p16Residual A b (xHat t) + deltaR t
  update_equation : ∀ t,
    xHatNext t = xHat t + correctionHat t + deltaX t
  correction_residual_bound : ∀ t,
    p16VecNorm (residualHat t - p16MatVec A (correctionHat t)) ≤
      w t * p16VecNorm (p16Residual A b (xHat t)) +
        omega t *
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHatNext t))
  residual_error_bound : ∀ t,
    p16VecNorm (deltaR t) ≤
      epsilonR t *
        (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat t))
  update_error_bound : ∀ t,
    p16VecNorm (deltaX t) ≤ epsilonU t * p16VecNorm (xHatNext t)
  epsilonR_nonneg : ∀ t, 0 ≤ epsilonR t
  epsilonU_nonneg : ∀ t, 0 ≤ epsilonU t
  w_nonneg : ∀ t, 0 ≤ w t
  omega_nonneg : ∀ t, 0 ≤ omega t
  epsilonR_tendsto_zero : Filter.Tendsto epsilonR l (nhds 0)
  epsilonU_tendsto_zero : Filter.Tendsto epsilonU l (nhds 0)
  iterate_norm_comparison :
    p16FirstOrderLeAt l scale
      (fun t ↦ p16VecNorm (xHat t))
      (fun t ↦ p16VecNorm (xHatNext t))

/-- Frobenius condition number `kappa_F(A)` represented with the certified
inverse that occurs in the T3 execution model. -/
noncomputable def p16ConditionNumberF {n : ℕ}
    (A Ainv : P16Matrix n) : ℝ :=
  p16FrobNorm Ainv * p16FrobNorm A

/-- A rectangular real matrix used for one Arnoldi restart. -/
abbrev P16RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

/-- Exact rectangular matrix-vector multiplication. -/
noncomputable def p16RectMatVec {m k : ℕ} (A : P16RectMatrix m k)
    (x : P16Vector k) : P16Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

/-- Exact multiplication of a square matrix by a rectangular matrix. -/
noncomputable def p16SquareRectMul {n k : ℕ} (A : P16Matrix n)
    (B : P16RectMatrix n k) : P16RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

/-- Exact multiplication of two conforming rectangular matrices. -/
noncomputable def p16RectMatMul {m k q : ℕ} (A : P16RectMatrix m k)
    (B : P16RectMatrix k q) : P16RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

/-- Frobenius norm for a rectangular matrix. -/
noncomputable def p16RectFrobNorm {m k : ℕ}
    (A : P16RectMatrix m k) : ℝ :=
  ‖A‖

/-- Append a scaled right-hand side to a rectangular matrix. This is the
matrix `[b * phi, C]` occurring in the key-dimension condition (3.7). -/
noncomputable def p16Augment {n k : ℕ} (b : P16Vector n)
    (phi : ℝ) (C : P16RectMatrix n k) : P16RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i * phi) (fun j ↦ C i j)

/-- A lower-gain certificate. It is the inequality form of a lower bound on
the smallest singular value and avoids choosing singular vectors. -/
def p16MinGainAtLeast {m k : ℕ} (A : P16RectMatrix m k)
    (sigma : ℝ) : Prop :=
  ∀ x : P16Vector k, sigma * p16VecNorm x ≤ p16VecNorm (p16RectMatVec A x)

/-- A unit vector witnessing numerical rank deficiency at tolerance `delta`.
This is the witness form of the upper singular-value condition (3.7). -/
def p16NearRankDeficient {m k : ℕ} (A : P16RectMatrix m k)
    (delta : ℝ) : Prop :=
  ∃ x : P16Vector k,
    p16VecNorm x = 1 ∧ p16VecNorm (p16RectMatVec A x) ≤ delta

/-- Exact least-squares optimality, used to record line 6 of restarted
MOD-GMRES without prescribing a particular solver implementation. -/
def p16IsLeastSquaresSolution {m k : ℕ} (A : P16RectMatrix m k)
    (b : P16Vector m) (y : P16Vector k) : Prop :=
  ∀ z : P16Vector k,
    p16VecNorm (b - p16RectMatVec A y) ≤
      p16VecNorm (b - p16RectMatVec A z)

/-- One explicit nonnegative bivariate polynomial standing for an occurrence
of the paper's unspecified low-degree factor `c(n,k)`. -/
structure P16PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

/-- Evaluation of a recorded low-degree polynomial factor. -/
noncomputable def p16PolynomialFactorValue (c : P16PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

/-- The paper's qualitative `Lambda << 1`: along the precision regime,
`Lambda` tends to zero and is eventually a nonnegative strict contraction. -/
def p16MuchLessThanOneAt {ι : Type*} (l : Filter ι)
    (lambda : ι → ℝ) : Prop :=
  Filter.Tendsto lambda l (nhds 0) ∧
    ∀ᶠ t in l, 0 ≤ lambda t ∧ lambda t < 1

/-- Actual forward error from printed page 1942. -/
noncomputable def p16ForwardError {n : ℕ} (x xHat : P16Vector n) : ℝ :=
  p16VecNorm (xHat - x) / p16VecNorm x

/-- The normalized true residual used as the actual backward error throughout
the paper. -/
noncomputable def p16BackwardError {n : ℕ} (A : P16Matrix n)
    (b xHat : P16Vector n) : ℝ :=
  p16NormalizedResidual A b xHat

/-- One fully stored, low-precision MGS-Arnoldi correction solve at a restart.

The raw fields record lines 4--7 of Algorithm 2, the residual cast, the
Arnoldi relation, the backward-stable least-squares solve, correction
formation, and witness forms of conditions (3.5)--(3.8). The last fields are
the correction-level consequences supplied by the Section 5.3 MGS-GMRES
analysis. They stop before the high-precision residual/update composition that
is the conclusion of Theorem 6.3. -/
structure P16LowPrecisionMGSRestart {n : ℕ} {ι : Type*}
    (l : Filter ι) (scale : ι → ℝ)
    (A Ainv : P16Matrix n) (b xExact : P16Vector n)
    (xCurrent xNext residualHat correctionHat : ι → P16Vector n)
    (uLow : ι → ℝ) (poly : P16PolynomialFactor) where
  keyDimension : ℕ
  keyDimension_pos : 0 < keyDimension
  keyDimension_le : keyDimension ≤ n
  basis : ι → P16RectMatrix n keyDimension
  basisNext : ι → P16RectMatrix n (keyDimension + 1)
  hessenberg : ι → P16RectMatrix (keyDimension + 1) keyDimension
  arnoldiError : ι → P16RectMatrix n keyDimension
  arnoldi_relation : ∀ t,
    p16SquareRectMul A (basis t) =
      p16RectMatMul (basisNext t) (hessenberg t) + arnoldiError t
  residualLow : ι → P16Vector n
  residualCastError : ι → P16Vector n
  residual_cast_equation : ∀ t,
    residualLow t = residualHat t + residualCastError t
  residual_cast_bound : ∀ t,
    p16VecNorm (residualCastError t) ≤ uLow t * p16VecNorm (residualHat t)
  arnoldiProduct : ι → P16RectMatrix n keyDimension
  arnoldiProductError : ι → P16RectMatrix n keyDimension
  arnoldi_product_equation : ∀ t,
    arnoldiProduct t = p16SquareRectMul A (basis t) + arnoldiProductError t
  epsilonC : ι → ℝ
  epsilonB : ι → ℝ
  epsilonLS : ι → ℝ
  epsilonX : ι → ℝ
  arnoldi_product_bound : ∀ t,
    p16RectFrobNorm (arnoldiProductError t) ≤
      epsilonC t * p16RectFrobNorm (p16SquareRectMul A (basis t))
  leastSquaresRhsError : ι → P16Vector n
  leastSquaresMatrixError : ι → P16RectMatrix n keyDimension
  leastSquaresY : ι → P16Vector keyDimension
  least_squares_solution : ∀ t,
    p16IsLeastSquaresSolution
      (arnoldiProduct t + leastSquaresMatrixError t)
      (residualLow t + leastSquaresRhsError t) (leastSquaresY t)
  least_squares_rhs_bound : ∀ t,
    p16VecNorm (leastSquaresRhsError t) ≤
      epsilonLS t * p16VecNorm (residualLow t)
  least_squares_matrix_bound : ∀ t,
    p16RectFrobNorm (leastSquaresMatrixError t) ≤
      epsilonLS t * p16RectFrobNorm (arnoldiProduct t)
  correctionFormationError : ι → P16Vector n
  correction_formation_equation : ∀ t,
    correctionHat t =
      p16RectMatVec (basis t) (leastSquaresY t) + correctionFormationError t
  correction_formation_bound : ∀ t,
    p16VecNorm (correctionFormationError t) ≤
      epsilonX t *
        p16RectFrobNorm (basis t) * p16VecNorm (leastSquaresY t)
  accuracy_nonneg : ∀ t,
    0 ≤ epsilonC t ∧ 0 ≤ epsilonB t ∧ 0 ≤ epsilonLS t ∧ 0 ≤ epsilonX t
  accuracy_tendsto_zero :
    Filter.Tendsto epsilonC l (nhds 0) ∧
      Filter.Tendsto epsilonB l (nhds 0) ∧
      Filter.Tendsto epsilonLS l (nhds 0) ∧
      Filter.Tendsto epsilonX l (nhds 0)
  basisLowerGain : ι → ℝ
  imageLowerGain : ι → ℝ
  basis_gain : ∀ t, p16MinGainAtLeast (basis t) (basisLowerGain t)
  image_gain : ∀ t,
    p16MinGainAtLeast (p16SquareRectMul A (basis t)) (imageLowerGain t)
  basis_not_numerically_rank_deficient : ∀ t,
    epsilonX t * p16RectFrobNorm (basis t) < basisLowerGain t
  key_near_dependence : keyDimension < n → ∀ t phi, 0 < phi →
    p16NearRankDeficient
      (p16Augment (residualLow t) phi (arnoldiProduct t))
      (p16PolynomialFactorValue poly n keyDimension *
        (epsilonC t + epsilonB t + epsilonLS t) *
        p16RectFrobNorm
          (p16Augment (residualLow t) phi (arnoldiProduct t)))
  key_image_full_rank : ∀ t,
    (epsilonC t + epsilonB t + epsilonLS t) *
        p16RectFrobNorm (arnoldiProduct t) < imageLowerGain t
  localFactor : ℝ
  localFactor_nonneg : 0 ≤ localFactor
  localFactor_polynomial_bound :
    localFactor ≤ p16PolynomialFactorValue poly n keyDimension
  localFactor_uniform_bound :
    p16PolynomialFactorValue poly n keyDimension ≤
      p16PolynomialFactorValue poly n n
  backwardFactor : ι → ℝ
  forwardFactor : ι → ℝ
  factors_nonneg : ∀ t, 0 ≤ backwardFactor t ∧ 0 ≤ forwardFactor t
  backward_factor_bound : ∀ t,
    backwardFactor t ≤
      localFactor * uLow t * p16ConditionNumberF A Ainv
  forward_factor_bound : ∀ t,
    forwardFactor t ≤
      localFactor * uLow t * p16ConditionNumberF A Ainv
  backward_correction_bound :
    p16FirstOrderLeAt l scale
      (fun t ↦
        p16VecNorm (residualHat t - p16MatVec A (correctionHat t)) /
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xNext t)))
      (fun t ↦ backwardFactor t * p16BackwardError A b (xCurrent t))
  forward_correction_bound :
    p16FirstOrderLeAt l scale
      (fun t ↦
        p16VecNorm (xCurrent t + correctionHat t - xExact) /
          p16VecNorm xExact)
      (fun t ↦ forwardFactor t * p16ForwardError xExact (xCurrent t))

/-- A complete abstract-real execution certificate for the unpreconditioned
mixed-precision restarted MGS-GMRES process of Theorem 6.3. The equations are
the paper's standard-model equations; using reals means underflow, overflow,
NaNs, and infinities are excluded. -/
structure P16MixedPrecisionGMRESRun {n : ℕ} {ι : Type*} (l : Filter ι) where
  dimension_pos : 0 < n
  A : P16Matrix n
  Ainv : P16Matrix n
  b : P16Vector n
  xExact : P16Vector n
  xHat : ℕ → ι → P16Vector n
  residualHat : ℕ → ι → P16Vector n
  correctionHat : ℕ → ι → P16Vector n
  residualError : ℕ → ι → P16Vector n
  updateError : ℕ → ι → P16Vector n
  uHigh : ι → ℝ
  uLow : ι → ℝ
  polynomialFactor : P16PolynomialFactor
  b_nonzero : b ≠ 0
  nonsingular : p16IsNonsingular A
  left_inverse_action : ∀ (z : P16Vector n),
    p16MatVec Ainv (p16MatVec A z) = z
  right_inverse_action : ∀ (z : P16Vector n),
    p16MatVec A (p16MatVec Ainv z) = z
  exact_solution : p16MatVec A xExact = b
  uHigh_nonneg : ∀ t, 0 ≤ uHigh t
  uLow_nonneg : ∀ t, 0 ≤ uLow t
  uHigh_le_uLow : ∀ t, uHigh t ≤ uLow t
  uHigh_tendsto_zero : Filter.Tendsto uHigh l (nhds 0)
  uLow_tendsto_zero : Filter.Tendsto uLow l (nhds 0)
  high_gamma_valid : ∀ t, GammaValid (uHigh t) n
  residual_equation : ∀ i t,
    residualHat i t = p16Residual A b (xHat i t) + residualError i t
  residual_error_bound : ∀ i t j,
    |residualError i t j| ≤
      gamma (uHigh t) n *
        (|b j| +
          p16MatVec (fun row col ↦ |A row col|)
            (fun col ↦ |xHat i t col|) j)
  update_equation : ∀ i t,
    xHat (i + 1) t = xHat i t + correctionHat i t + updateError i t
  update_error_bound : ∀ i t j,
    |updateError i t j| ≤ uHigh t * |xHat (i + 1) t j|
  restart : ∀ i,
    P16LowPrecisionMGSRestart l (fun t ↦ uHigh t + uLow t)
      A Ainv b xExact (xHat i) (xHat (i + 1))
      (residualHat i) (correctionHat i) uLow polynomialFactor
  iterate_norm_current_next : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (xHat i t))
      (fun t ↦ p16VecNorm (xHat (i + 1) t))
  iterate_norm_next_solution : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (xHat (i + 1) t))
      (fun _ ↦ p16VecNorm xExact)
  backward_high_roundoff_bound : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦
        (p16VecNorm (residualError i t) +
            p16VecNorm (p16MatVec A (updateError i t))) /
          (p16VecNorm b + p16FrobNorm A * p16VecNorm (xHat (i + 1) t)))
      (fun t ↦
        p16PolynomialFactorValue polynomialFactor n n * uHigh t)
  forward_high_roundoff_bound : ∀ i,
    p16FirstOrderLeAt l (fun t ↦ uHigh t + uLow t)
      (fun t ↦ p16VecNorm (updateError i t) / p16VecNorm xExact)
      (fun t ↦
        p16PolynomialFactorValue polynomialFactor n n * uHigh t *
          p16ConditionNumberF A Ainv)

/-- Combined high/low precision scale used for retained second-order terms. -/
noncomputable def p16MixedScale {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ run.uHigh t + run.uLow t

/-- Uniform contraction envelope in equation (6.17). The value at `(n,n)`
dominates every restart-dependent `c(n,k_i)` recorded by the run. -/
noncomputable def p16MixedContraction {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦
    p16PolynomialFactorValue run.polynomialFactor n n * run.uLow t *
      p16ConditionNumberF run.A run.Ainv

/-- High-precision backward-error floor in equation (6.18). -/
noncomputable def p16BackwardFloor {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦ p16PolynomialFactorValue run.polynomialFactor n n * run.uHigh t

/-- High-precision forward-error floor in equation (6.18). -/
noncomputable def p16ForwardFloor {n : ℕ} {ι : Type*} {l : Filter ι}
    (run : P16MixedPrecisionGMRESRun (n := n) l) : ι → ℝ :=
  fun t ↦
    p16PolynomialFactorValue run.polynomialFactor n n * run.uHigh t *
      p16ConditionNumberF run.A run.Ainv

end HighamBench
```
