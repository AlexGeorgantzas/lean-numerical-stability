# Declaration dossier for P20-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p20_t3_multiword_forward_error
    {m n q p : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (execution : P20Theorem41Execution m n q p ι l) :
    p20FirstOrderLeAt l (p20MultiwordPrecisionScale execution.run)
        (p20MultiwordForwardError execution.run)
        (fun t =>
          p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20AccumUnitRoundoff execution.run.model t)
              (p20ModelScalingThreshold n execution.run.model t)
              (p20InputUnderflowEnvelope execution.run.model t)
              (p20AccumUnderflowEnvelope execution.run.model t))
            execution.run.A execution.run.B) ∧
      ∀ t,
        p20MultiNarrowCoefficient n p
            (p20InputUnitRoundoff execution.run.model t)
            (p20AccumUnitRoundoff execution.run.model t)
            (p20ModelScalingThreshold n execution.run.model t)
            (p20InputUnderflowEnvelope execution.run.model t)
            (p20AccumUnderflowEnvelope execution.run.model t) =
          p20MultiRangeFreeCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20AccumUnitRoundoff execution.run.model t) +
            p20MultiInputUnderflowCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20ModelScalingThreshold n execution.run.model t)
              (p20InputUnderflowEnvelope execution.run.model t) +
            p20MultiAccumUnderflowCoefficient n p
              (p20ModelScalingThreshold n execution.run.model t)
              (p20AccumUnderflowEnvelope execution.run.model t)
```

## Elaborated target type

```lean
∀ {m n q p : Nat} {ι : Type u_1} {l : Filter ι} [l.NeBot] (execution : HighamBench.P20Theorem41Execution m n q p ι l),
  And
    (HighamBench.p20FirstOrderLeAt l (HighamBench.p20MultiwordPrecisionScale execution.run)
      (HighamBench.p20MultiwordForwardError execution.run) fun t =>
      HighamBench.p20NormwiseEnvelope
        (HighamBench.p20MultiNarrowCoefficient n p (HighamBench.p20InputUnitRoundoff execution.run.model t)
          (HighamBench.p20AccumUnitRoundoff execution.run.model t)
          (HighamBench.p20ModelScalingThreshold n execution.run.model t)
          (HighamBench.p20InputUnderflowEnvelope execution.run.model t)
          (HighamBench.p20AccumUnderflowEnvelope execution.run.model t))
        execution.run.A execution.run.B)
    (∀ (t : ι),
      Eq
        (HighamBench.p20MultiNarrowCoefficient n p (HighamBench.p20InputUnitRoundoff execution.run.model t)
          (HighamBench.p20AccumUnitRoundoff execution.run.model t)
          (HighamBench.p20ModelScalingThreshold n execution.run.model t)
          (HighamBench.p20InputUnderflowEnvelope execution.run.model t)
          (HighamBench.p20AccumUnderflowEnvelope execution.run.model t))
        (instHAdd.hAdd
          (instHAdd.hAdd
            (HighamBench.p20MultiRangeFreeCoefficient n p (HighamBench.p20InputUnitRoundoff execution.run.model t)
              (HighamBench.p20AccumUnitRoundoff execution.run.model t))
            (HighamBench.p20MultiInputUnderflowCoefficient n p (HighamBench.p20InputUnitRoundoff execution.run.model t)
              (HighamBench.p20ModelScalingThreshold n execution.run.model t)
              (HighamBench.p20InputUnderflowEnvelope execution.run.model t)))
          (HighamBench.p20MultiAccumUnderflowCoefficient n p
            (HighamBench.p20ModelScalingThreshold n execution.run.model t)
            (HighamBench.p20AccumUnderflowEnvelope execution.run.model t))))
```

## Fully explicit elaborated target type

```lean
∀ {m n q p : Nat} {ι : Type u_1} {l : Filter.{u_1} ι} [@Filter.NeBot.{u_1} ι l]
  (execution : HighamBench.P20Theorem41Execution.{u_1} m n q p ι l),
  And
    (@HighamBench.p20FirstOrderLeAt.{u_1} ι l
      (@HighamBench.p20MultiwordPrecisionScale.{u_1} m n q p ι
        (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
      (@HighamBench.p20MultiwordForwardError.{u_1} m n q p ι
        (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
      fun (t : ι) =>
      @HighamBench.p20NormwiseEnvelope m n q
        (HighamBench.p20MultiNarrowCoefficient n p
          (@HighamBench.p20InputUnitRoundoff.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20AccumUnitRoundoff.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20InputUnderflowEnvelope.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20AccumUnderflowEnvelope.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t))
        (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι
          (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
        (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι
          (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution)))
    (∀ (t : ι),
      @Eq.{1} Real
        (HighamBench.p20MultiNarrowCoefficient n p
          (@HighamBench.p20InputUnitRoundoff.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20AccumUnitRoundoff.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20InputUnderflowEnvelope.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t)
          (@HighamBench.p20AccumUnderflowEnvelope.{u_1} ι
            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
              (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
            t))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (HighamBench.p20MultiRangeFreeCoefficient n p
              (@HighamBench.p20InputUnitRoundoff.{u_1} ι
                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                  (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
                t)
              (@HighamBench.p20AccumUnitRoundoff.{u_1} ι
                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                  (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
                t))
            (HighamBench.p20MultiInputUnderflowCoefficient n p
              (@HighamBench.p20InputUnitRoundoff.{u_1} ι
                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                  (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
                t)
              (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                  (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
                t)
              (@HighamBench.p20InputUnderflowEnvelope.{u_1} ι
                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                  (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
                t)))
          (HighamBench.p20MultiAccumUnderflowCoefficient n p
            (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
              (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
              t)
            (@HighamBench.p20AccumUnderflowEnvelope.{u_1} ι
              (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι
                (@HighamBench.P20Theorem41Execution.run.{u_1} m n q p ι l execution))
              t))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P20Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P20Definitions` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Real.Sqrt`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P20MultiwordRun.A`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9594cae7a57d44827ec93e7f76c28c0a1a8e6230a411eec2b095b16f7a2966e3`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.4
```

### D002: `HighamBench.P20MultiwordRun.B`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `9c67bfedcd197f366d508e5bd9df25a16a76d40081a3374f8a376548cba5ddb6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.5
```

### D003: `HighamBench.P20MultiwordRun.model`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8be01d8ad1d537a6367b7523510f0e9470719882b08c7e39ddbf8c2f567be8e6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → HighamBench.P20Model1 ι
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → HighamBench.P20Model1.{u_1} ι
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.3
```

### D004: `HighamBench.P20Theorem41Execution`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `416516a9510181b79d744eff2caab5d64f7243e54d03c62febd24c0db946ad05`

Type:

```lean
Nat → Nat → Nat → Nat → (ι : Type u_1) → Filter ι → Type u_1
```

Fully explicit type:

```lean
(m n q p : Nat) → (ι : Type u_1) → (l : Filter.{u_1} ι) → Type u_1
```

### D005: `HighamBench.P20Theorem41Execution.run`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fed6503d9202666af3f4554377177f5cd361a42d30bb6bbd290b900528277d12`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} → HighamBench.P20Theorem41Execution m n q p ι l → HighamBench.P20MultiwordRun m n q p ι
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (self : HighamBench.P20Theorem41Execution.{u_1} m n q p ι l) → HighamBench.P20MultiwordRun.{u_1} m n q p ι
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι l self => self.1
```

### D006: `HighamBench.p20AccumUnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4c3c15a2681fa86b178a756216726f84a6b209b2f9fbdf991f246cc135fcd2d2`

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
fun {ι} model t => HighamBench.p20FormatUnderflowEnvelope model.accumulationFormat t
```

### D007: `HighamBench.p20AccumUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `90703ecd8044f6d933fb829dec2b80806bc4ff0e497a031e28b00d72cabcd19e`

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
fun {ι} model t => HighamBench.p20FormatUnitRoundoff model.accumulationFormat t
```

### D008: `HighamBench.p20FirstOrderLeAt`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1521ce8a7cd811a1f00f9d6fa76581378be240fcef6e441dd7723db094ab6e3f`

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
    And (HighamBench.p20SecondOrderAt l scale remainder)
      (Filter.Eventually (fun t => Real.instLE.le (lhs t) (instHAdd.hAdd (rhs t) (abs (remainder t)))) l)
```

### D009: `HighamBench.p20InputUnderflowEnvelope`

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

### D010: `HighamBench.p20InputUnitRoundoff`

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

### D011: `HighamBench.p20ModelScalingThreshold`

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

### D012: `HighamBench.p20MultiAccumUnderflowCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5aeb2436e762793f876c56e261949985186ece9b87b7642526cca63726f5cbc8`

Type:

```lean
Nat → Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n p : Nat) → (theta Gmin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p theta Gmin =>
  instHMul.hMul
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (instHMul.hMul 2 p.cast) (instHAdd.hAdd p.cast 1)) (instHPow.hPow n.cast 2))
      (instHPow.hPow (Real.instInv.inv theta) 2))
    Gmin
```

### D013: `HighamBench.p20MultiInputUnderflowCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e81b283d73a42696b3ad126f193ca40cb6314201f6a0894d43f37fb73d5a2f56`

Type:

```lean
Nat → Nat → Real → Real → Real → Real
```

Fully explicit type:

```lean
(n p : Nat) → (u theta gmin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u theta gmin =>
  instHMul.hMul
    (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 n.cast) (instHPow.hPow u (instHSub.hSub p 1)))
      (Real.instInv.inv theta))
    gmin
```

### D014: `HighamBench.p20MultiNarrowCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `caa0600e2ab6bac4a1950fef389ea5430e501684280b91c745f1ee261a9ba7c7`

Type:

```lean
Nat → Nat → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
(n p : Nat) → (u U theta gmin Gmin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u U theta gmin Gmin =>
  instHAdd.hAdd
    (instHAdd.hAdd (HighamBench.p20MultiRangeFreeCoefficient n p u U)
      (HighamBench.p20MultiInputUnderflowCoefficient n p u theta gmin))
    (HighamBench.p20MultiAccumUnderflowCoefficient n p theta Gmin)
```

### D015: `HighamBench.p20MultiRangeFreeCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2487e9b14eff0b27a720d879c028573ed442dba650abf6c1634f308d44e7e364`

Type:

```lean
Nat → Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n p : Nat) → (u U : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p u U =>
  instHAdd.hAdd (HighamBench.p20MultiInputRoundingCoefficient p u) (HighamBench.p20MultiAccumRoundingCoefficient n p U)
```

### D016: `HighamBench.p20MultiwordForwardError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cc3dbc71a874f6b6ec77ae52e0346c81d20c3ea2892c754a4633ab82e4e6181d`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → (t : ι) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  HighamBench.p20InfNormRect
    (instHSub.hSub (run.computed t) (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
```

### D017: `HighamBench.p20MultiwordPrecisionScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `92d7b625d010a5e2f91f00abf58e263ee2c8991480c39169b02129316ec5f3f2`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHAdd.hAdd (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) p)
        (instHMul.hMul
          (instHMul.hMul (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) (instHSub.hSub p 1))
            (Real.instInv.inv (HighamBench.p20ModelScalingThreshold n run.model t)))
          (HighamBench.p20InputUnderflowEnvelope run.model t)))
      (HighamBench.p20AccumUnitRoundoff run.model t))
    (instHMul.hMul (instHPow.hPow (Real.instInv.inv (HighamBench.p20ModelScalingThreshold n run.model t)) 2)
      (HighamBench.p20AccumUnderflowEnvelope run.model t))
```

### D018: `HighamBench.p20NormwiseEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8b3df00dc379b26060ad35527c8889510927aa8aae6ac3b90b480d9ea8ecb0de`

Type:

```lean
{m n q : Nat} → Real → (Fin m → Fin n → Real) → (Fin n → Fin q → Real) → Real
```

Fully explicit type:

```lean
{m n q : Nat} → (coefficient : Real) → (A : Fin m → Fin n → Real) → (B : Fin n → Fin q → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q} coefficient A B =>
  instHMul.hMul (instHMul.hMul coefficient (HighamBench.p20InfNormRect A)) (HighamBench.p20InfNormRect B)
```

### D019: `HighamBench.P20Matrix`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8816b1a67d28d646055c444bb08aa6cc7cb0918adb37ddbe0e4b64f19a1937b4`

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

### D020: `HighamBench.P20Model1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `e061b0ae3b92688463023faf203412bd4115dc0ed0667840f7767652f00b9019`

Type:

```lean
Type u_1 → Type u_1
```

Fully explicit type:

```lean
(ι : Type u_1) → Type u_1
```

### D021: `HighamBench.P20Model1.accumulationFormat`

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

### D022: `HighamBench.P20Model1.inputFormat`

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

### D023: `HighamBench.P20MultiwordRun`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `f178a3d0f984cdaa9efc033435294822cc599bf33537fc8e7c0e07199286d2fc`

Type:

```lean
Nat → Nat → Nat → Nat → Type u_1 → Type u_1
```

Fully explicit type:

```lean
(m n q p : Nat) → (ι : Type u_1) → Type u_1
```

### D024: `HighamBench.P20MultiwordRun.computed`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9b51e165c494e180ef797bc7a505ebfe42b1db813e25bc6ee4dbe6374540037a`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.16
```

### D025: `HighamBench.P20Theorem41Execution.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `0f9e19e81cf10969d8983d8f14f1d8fea0589fccb6adf3bb96b8f73f1fc2bed4`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      (run : HighamBench.P20MultiwordRun m n q p ι) →
        HighamBench.P20MultiwordForwardAnalysis run → HighamBench.P20Theorem41Execution m n q p ι l
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) →
        (analysis : @HighamBench.P20MultiwordForwardAnalysis.{u_1} m n q p ι l run) →
          HighamBench.P20Theorem41Execution.{u_1} m n q p ι l
```

### D026: `HighamBench.p20FormatMaxFinite`

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

### D027: `HighamBench.p20FormatUnderflowEnvelope`

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

### D028: `HighamBench.p20FormatUnitRoundoff`

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

### D029: `HighamBench.p20InfNormRect`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `85f0c53817ee468470f6b18e6390691148158e3a270bf87d2feb43e175ec9e0a`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A =>
  have rowSum := fun i => Finset.univ.sum fun j => SeminormedAddGroup.toNNNorm.nnnorm (A i j);
  (Finset.univ.sup rowSum).toReal
```

### D030: `HighamBench.p20IsPowerOfTwo._proof_1`

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

### D031: `HighamBench.p20MultiAccumRoundingCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f6f3cf93f5f3ae2f8f71ee9bb65c6b5bdb6b612575c6584b8ad6e0e9d7466b7a`

Type:

```lean
Nat → Nat → Real → Real
```

Fully explicit type:

```lean
(n p : Nat) → (U : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p U => instHMul.hMul (instHAdd.hAdd n.cast (instHPow.hPow p.cast 2)) U
```

### D032: `HighamBench.p20MultiInputRoundingCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d95881c72218c764905e4c1450dd882eda6fa4a4c4a6840f2ec5044e3981f45a`

Type:

```lean
Nat → Real → Real
```

Fully explicit type:

```lean
(p : Nat) → (u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun p u => instHMul.hMul (instHAdd.hAdd p.cast 1) (instHPow.hPow u p)
```

### D033: `HighamBench.p20ScalingThreshold`

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

### D034: `HighamBench.p20SecondOrderAt`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0e067e47238962db3263b46553181a9e7fd40da11726a292ab40026a81435288`

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

### D035: `HighamBench.p20SingleInputUnderflowBound._proof_1`

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

### D036: `HighamBench.P20BinaryFormatFamily`

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

### D037: `HighamBench.P20BinaryFormatFamily.hasSubnormals`

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

### D038: `HighamBench.P20BinaryFormatFamily.maxExponent`

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

### D039: `HighamBench.P20BinaryFormatFamily.minExponent`

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

### D040: `HighamBench.P20BinaryFormatFamily.precision`

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

### D041: `HighamBench.P20Model1.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
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

### D042: `HighamBench.P20MultiwordForwardAnalysis`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `85887da83eb47ab9a6773f4132be09426ddc4f08decdc172ba510784de9131ce`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → {l : Filter ι} → HighamBench.P20MultiwordRun m n q p ι → Type u_1
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → {l : Filter.{u_1} ι} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → Type u_1
```

### D043: `HighamBench.P20MultiwordRun.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `f097b804cc549a67af75c82d98427f5897fa6da7f3ada1c1915d8516a0be1aaf`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    And (instLTNat.lt 0 m) (And (instLTNat.lt 0 n) (instLTNat.lt 0 q)) →
      instLTNat.lt 0 p →
        (model : HighamBench.P20Model1 ι) →
          (A : HighamBench.P20Matrix m n) →
            (B : HighamBench.P20Matrix n q) →
              (rowScale : ι → Fin m → Real) →
                (columnScale : ι → Fin q → Real) →
                  (∀ (t : ι) (i : Fin m),
                      HighamBench.p20MaximalPowerTwoScale (HighamBench.p20ModelScalingThreshold n model t)
                        (HighamBench.p20InfNormVec (A i)) (rowScale t i)) →
                    (∀ (t : ι) (j : Fin q),
                        HighamBench.p20MaximalPowerTwoScale (HighamBench.p20ModelScalingThreshold n model t)
                          (HighamBench.p20InfNormVec fun i => B i j) (columnScale t j)) →
                      (∀ (t : ι) (i : Fin m) (j : Fin n),
                          Real.instLE.le (abs (HighamBench.p20ScaleRows (rowScale t) A i j))
                            (HighamBench.p20ModelScalingThreshold n model t)) →
                        (∀ (t : ι) (i : Fin n) (j : Fin q),
                            Real.instLE.le (abs (HighamBench.p20ScaleColumns B (columnScale t) i j))
                              (HighamBench.p20ModelScalingThreshold n model t)) →
                          (Aword : ι → Fin p → HighamBench.P20Matrix m n) →
                            (Bword : ι → Fin p → HighamBench.P20Matrix n q) →
                              (∀ (t : ι) (i : Fin p) (row : Fin m) (col : Fin n),
                                  Eq (Aword t i row col)
                                    (model.inputRound t
                                      (instHDiv.hDiv
                                        (instHSub.hSub (HighamBench.p20ScaleRows (rowScale t) A row col)
                                          ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                            instHMul.hMul
                                              (instHPow.hPow (HighamBench.p20InputUnitRoundoff model t) k.val)
                                              (Aword t k row col)))
                                        (instHPow.hPow (HighamBench.p20InputUnitRoundoff model t) i.val)))) →
                                (∀ (t : ι) (i : Fin p) (row : Fin n) (col : Fin q),
                                    Eq (Bword t i row col)
                                      (model.inputRound t
                                        (instHDiv.hDiv
                                          (instHSub.hSub (HighamBench.p20ScaleColumns B (columnScale t) row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (HighamBench.p20InputUnitRoundoff model t) k.val)
                                                (Bword t k row col)))
                                          (instHPow.hPow (HighamBench.p20InputUnitRoundoff model t) i.val)))) →
                                  (computed : ι → HighamBench.P20Matrix m q) →
                                    (∀ (t : ι),
                                        Eq (computed t)
                                          (HighamBench.p20UnscaleProduct (rowScale t) (columnScale t)
                                            (HighamBench.p20RetainedWordProduct (model.accumulationRound t)
                                              (HighamBench.p20InputUnitRoundoff model t) (Aword t) (Bword t)))) →
                                      HighamBench.P20MultiwordRun m n q p ι
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    (dimension_pos :
        And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
          (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q))) →
      (word_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
        (model : HighamBench.P20Model1.{u_1} ι) →
          (A : HighamBench.P20Matrix m n) →
            (B : HighamBench.P20Matrix n q) →
              (rowScale : ι → Fin m → Real) →
                (columnScale : ι → Fin q → Real) →
                  (row_scaling_rule :
                      ∀ (t : ι) (i : Fin m),
                        HighamBench.p20MaximalPowerTwoScale (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)
                          (@HighamBench.p20InfNormVec n (A i)) (rowScale t i)) →
                    (column_scaling_rule :
                        ∀ (t : ι) (j : Fin q),
                          HighamBench.p20MaximalPowerTwoScale (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)
                            (@HighamBench.p20InfNormVec n fun (i : Fin n) => B i j) (columnScale t j)) →
                      (scaled_A_bound :
                          ∀ (t : ι) (i : Fin m) (j : Fin n),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@HighamBench.p20ScaleRows m n (rowScale t) A i j))
                              (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)) →
                        (scaled_B_bound :
                            ∀ (t : ι) (i : Fin n) (j : Fin q),
                              @LE.le.{0} Real Real.instLE
                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                  (@HighamBench.p20ScaleColumns n q B (columnScale t) i j))
                                (@HighamBench.p20ModelScalingThreshold.{u_1} ι n model t)) →
                          (Aword : ι → Fin p → HighamBench.P20Matrix m n) →
                            (Bword : ι → Fin p → HighamBench.P20Matrix n q) →
                              (Aword_equation :
                                  ∀ (t : ι) (i : Fin p) (row : Fin m) (col : Fin n),
                                    @Eq.{1} Real (Aword t i row col)
                                      (@HighamBench.P20Model1.inputRound.{u_1} ι model t
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                            (@HighamBench.p20ScaleRows m n (rowScale t) A row col)
                                            (@Finset.sum.{0, 0} (Fin p) Real Real.instAddCommMonoid
                                              (@Finset.filter.{0} (Fin p)
                                                (fun (k : Fin p) =>
                                                  @LT.lt.{0} Nat instLTNat (@Fin.val p k) (@Fin.val p i))
                                                (fun (a : Fin p) => Nat.decLt (@Fin.val p a) (@Fin.val p i))
                                                (@Finset.univ.{0} (Fin p) (Fin.fintype p)))
                                              fun (k : Fin p) =>
                                              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                  (@instHPow.{0, 0} Real Nat
                                                    (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                  (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t) (@Fin.val p k))
                                                (Aword t k row col)))
                                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                                            (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                            (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t) (@Fin.val p i))))) →
                                (Bword_equation :
                                    ∀ (t : ι) (i : Fin p) (row : Fin n) (col : Fin q),
                                      @Eq.{1} Real (Bword t i row col)
                                        (@HighamBench.P20Model1.inputRound.{u_1} ι model t
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@HighamBench.p20ScaleColumns n q B (columnScale t) row col)
                                              (@Finset.sum.{0, 0} (Fin p) Real Real.instAddCommMonoid
                                                (@Finset.filter.{0} (Fin p)
                                                  (fun (k : Fin p) =>
                                                    @LT.lt.{0} Nat instLTNat (@Fin.val p k) (@Fin.val p i))
                                                  (fun (a : Fin p) => Nat.decLt (@Fin.val p a) (@Fin.val p i))
                                                  (@Finset.univ.{0} (Fin p) (Fin.fintype p)))
                                                fun (k : Fin p) =>
                                                @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                    (@instHPow.{0, 0} Real Nat
                                                      (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                    (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t) (@Fin.val p k))
                                                  (Bword t k row col)))
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                              (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t) (@Fin.val p i))))) →
                                  (computed : ι → HighamBench.P20Matrix m q) →
                                    (computed_equation :
                                        ∀ (t : ι),
                                          @Eq.{1} (HighamBench.P20Matrix m q) (computed t)
                                            (@HighamBench.p20UnscaleProduct m q (rowScale t) (columnScale t)
                                              (@HighamBench.p20RetainedWordProduct m n q p
                                                (@HighamBench.P20Model1.accumulationRound.{u_1} ι model t)
                                                (@HighamBench.p20InputUnitRoundoff.{u_1} ι model t) (Aword t)
                                                (Bword t)))) →
                                      HighamBench.P20MultiwordRun.{u_1} m n q p ι
```

### D044: `HighamBench.p20MaxFinite`

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

### D045: `HighamBench.p20UnderflowEnvelope`

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

### D046: `HighamBench.p20UnitRoundoff`

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

### D047: `HighamBench.P20BinaryFormatFamily.mk`

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

### D048: `HighamBench.P20Model1.accumulationRound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fad245ffc5c0bf3a444afa929cb5f38a2626fdc667cec06d4b2d3b8a8c6320a2`

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
fun ι self => self.12
```

### D049: `HighamBench.P20Model1.inputRound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D050: `HighamBench.P20MultiwordForwardAnalysis.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `68b2dd902c488fcefd9317577852aa6d458a77246a39d74b8c680201a1bd68c1`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter ι} →
      {run : HighamBench.P20MultiwordRun m n q p ι} →
        (data : HighamBench.P20MultiwordErrorData run) →
          (∀ (t : ι),
              Real.instLE.le (HighamBench.p20InfNormRect (HighamBench.p20InputRoundingContribution data t))
                (HighamBench.p20NormwiseEnvelope
                  (HighamBench.p20MultiInputRoundingCoefficient p (HighamBench.p20InputUnitRoundoff run.model t)) run.A
                  run.B)) →
            (∀ (t : ι),
                Real.instLE.le (HighamBench.p20InfNormRect (HighamBench.p20InputUnderflowContribution data t))
                  (HighamBench.p20NormwiseEnvelope
                    (HighamBench.p20MultiInputUnderflowCoefficient n p (HighamBench.p20InputUnitRoundoff run.model t)
                      (HighamBench.p20ModelScalingThreshold n run.model t)
                      (HighamBench.p20InputUnderflowEnvelope run.model t))
                    run.A run.B)) →
              (∀ (t : ι),
                  Real.instLE.le (HighamBench.p20InfNormRect (HighamBench.p20AccumRoundingContribution data t))
                    (HighamBench.p20NormwiseEnvelope
                      (HighamBench.p20MultiAccumRoundingCoefficient n p (HighamBench.p20AccumUnitRoundoff run.model t))
                      run.A run.B)) →
                (∀ (t : ι),
                    Real.instLE.le (HighamBench.p20InfNormRect (HighamBench.p20AccumUnderflowContribution data t))
                      (HighamBench.p20NormwiseEnvelope
                        (HighamBench.p20MultiAccumUnderflowCoefficient n p
                          (HighamBench.p20ModelScalingThreshold n run.model t)
                          (HighamBench.p20AccumUnderflowEnvelope run.model t))
                        run.A run.B)) →
                  (HighamBench.p20SecondOrderAt l (HighamBench.p20MultiwordPrecisionScale run) fun t =>
                      HighamBench.p20InfNormRect (HighamBench.p20ForwardRemainder run data t)) →
                    HighamBench.P20MultiwordForwardAnalysis run
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {l : Filter.{u_1} ι} →
      {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
        (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) →
          (input_rounding_bound :
              ∀ (t : ι),
                @LE.le.{0} Real Real.instLE
                  (@HighamBench.p20InfNormRect m q
                    (@HighamBench.p20InputRoundingContribution.{u_1} m n q p ι run data t))
                  (@HighamBench.p20NormwiseEnvelope m n q
                    (HighamBench.p20MultiInputRoundingCoefficient p
                      (@HighamBench.p20InputUnitRoundoff.{u_1} ι
                        (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t))
                    (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι run)
                    (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι run))) →
            (input_underflow_bound :
                ∀ (t : ι),
                  @LE.le.{0} Real Real.instLE
                    (@HighamBench.p20InfNormRect m q
                      (@HighamBench.p20InputUnderflowContribution.{u_1} m n q p ι run data t))
                    (@HighamBench.p20NormwiseEnvelope m n q
                      (HighamBench.p20MultiInputUnderflowCoefficient n p
                        (@HighamBench.p20InputUnitRoundoff.{u_1} ι
                          (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                        (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
                          (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                        (@HighamBench.p20InputUnderflowEnvelope.{u_1} ι
                          (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t))
                      (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι run)
                      (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι run))) →
              (accumulation_rounding_bound :
                  ∀ (t : ι),
                    @LE.le.{0} Real Real.instLE
                      (@HighamBench.p20InfNormRect m q
                        (@HighamBench.p20AccumRoundingContribution.{u_1} m n q p ι run data t))
                      (@HighamBench.p20NormwiseEnvelope m n q
                        (HighamBench.p20MultiAccumRoundingCoefficient n p
                          (@HighamBench.p20AccumUnitRoundoff.{u_1} ι
                            (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t))
                        (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι run)
                        (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι run))) →
                (accumulation_underflow_bound :
                    ∀ (t : ι),
                      @LE.le.{0} Real Real.instLE
                        (@HighamBench.p20InfNormRect m q
                          (@HighamBench.p20AccumUnderflowContribution.{u_1} m n q p ι run data t))
                        (@HighamBench.p20NormwiseEnvelope m n q
                          (HighamBench.p20MultiAccumUnderflowCoefficient n p
                            (@HighamBench.p20ModelScalingThreshold.{u_1} ι n
                              (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                            (@HighamBench.p20AccumUnderflowEnvelope.{u_1} ι
                              (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t))
                          (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι run)
                          (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι run))) →
                  (remainder_second_order :
                      @HighamBench.p20SecondOrderAt.{u_1} ι l
                        (@HighamBench.p20MultiwordPrecisionScale.{u_1} m n q p ι run) fun (t : ι) =>
                        @HighamBench.p20InfNormRect m q (@HighamBench.p20ForwardRemainder.{u_1} m n q p ι run data t)) →
                    @HighamBench.P20MultiwordForwardAnalysis.{u_1} m n q p ι l run
```

### D051: `HighamBench.p20InfNormVec`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D052: `HighamBench.p20MaximalPowerTwoScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D053: `HighamBench.p20MinNormal`

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

### D054: `HighamBench.p20RetainedWordProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `54b336ce4868ee145633cb139fd883806f827fa26cfa6a2fe2b32d8d0c9685d3`

Type:

```lean
{m n q p : Nat} →
  (Real → Real) →
    Real → (Fin p → HighamBench.P20Matrix m n) → (Fin p → HighamBench.P20Matrix n q) → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  (round : Real → Real) →
    (u : Real) →
      (Aword : Fin p → HighamBench.P20Matrix m n) →
        (Bword : Fin p → HighamBench.P20Matrix n q) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} round u Aword Bword row col =>
  List.foldl
    (fun sum pair =>
      round
        (instHAdd.hAdd sum
          (instHMul.hMul (instHPow.hPow u (instHAdd.hAdd pair.fst.val pair.snd.val))
            (HighamBench.p20AccumulatedInnerProduct round (Aword pair.fst row) fun k => Bword pair.snd k col))))
    0 (HighamBench.p20RetainedWordPairs p)
```

### D055: `HighamBench.p20ScaleColumns`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `378c6beb84502e2b56ff224e26171be0f80b1263c8d574e611b959c865a7073f`

Type:

```lean
{n q : Nat} → HighamBench.P20Matrix n q → (Fin q → Real) → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{n q : Nat} → (B : HighamBench.P20Matrix n q) → (mu : Fin q → Real) → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun {n q} B mu i j => instHMul.hMul (B i j) (mu j)
```

### D056: `HighamBench.p20ScaleRows`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `00f5599a51f7504fa6af21fe5f75dbc8584462339602b0cca6a3d151edb4518f`

Type:

```lean
{m n : Nat} → (Fin m → Real) → HighamBench.P20Matrix m n → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n : Nat} → (lambda : Fin m → Real) → (A : HighamBench.P20Matrix m n) → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n} lambda A i j => instHMul.hMul (lambda i) (A i j)
```

### D057: `HighamBench.p20UnderflowEnvelope.match_1`

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

### D058: `HighamBench.p20UnscaleProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f39885f324faf09cbe5e6c2bd4eae850670ec539979d0b37aaed2094bab7cc7b`

Type:

```lean
{m q : Nat} → (Fin m → Real) → (Fin q → Real) → HighamBench.P20Matrix m q → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m q : Nat} →
  (lambda : Fin m → Real) → (mu : Fin q → Real) → (C : HighamBench.P20Matrix m q) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m q} lambda mu C i j =>
  instHMul.hMul (instHMul.hMul (Real.instInv.inv (lambda i)) (C i j)) (Real.instInv.inv (mu j))
```

### D059: `HighamBench.P20MultiwordErrorData`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `5f3c858c4f89c05ccc0ed46c038e51f3ef417fb48f9424a25ece1ef566d7ed25`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → Type u_1
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → Type u_1
```

### D060: `HighamBench.p20AccumRoundingContribution`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f5aaa6aa0d03307189f851e6da09a8586ed614d024434ee292e7a15b3e84fb69`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t => data.accumulationRoundingError t
```

### D061: `HighamBench.p20AccumUnderflowContribution`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d3a8c32a78d3b89a2ee6cd7f72a1f53f38a3f6ee9a05ab2ca61e1747892a887d`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t => data.accumulationUnderflowError t
```

### D062: `HighamBench.p20AccumulatedInnerProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `85ce3b8c1ee59d62e0d9951b949ec2dc99ba00d4170e02662308816d384cbd6a`

Type:

```lean
{n : Nat} → (Real → Real) → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (round : Real → Real) → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} round x y =>
  List.foldl (fun sum product => round (instHAdd.hAdd sum product)) 0 (List.ofFn fun k => instHMul.hMul (x k) (y k))
```

### D063: `HighamBench.p20ForwardRemainder`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `6f6b2dcf16831723a067aadc66a4b35fa717345a2ca0149a7c0ce72dee226aa1`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    (run : HighamBench.P20MultiwordRun m n q p ι) →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) →
      (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run data t =>
  instHSub.hSub
    (instHSub.hSub
      (instHSub.hSub
        (instHSub.hSub (instHSub.hSub (run.computed t) (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
          (HighamBench.p20InputRoundingContribution data t))
        (HighamBench.p20InputUnderflowContribution data t))
      (HighamBench.p20AccumRoundingContribution data t))
    (HighamBench.p20AccumUnderflowContribution data t)
```

### D064: `HighamBench.p20InputRoundingContribution`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `31a7c0afe8475a9d0f0d38af1eabb4411434b0b9d3aacaecfe4b1e73d873384a`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t =>
  instHSub.hSub
    (instHSub.hSub
      (Matrix.neg.neg (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (data.AInputRoundingError t) run.B))
      (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A (data.BInputRoundingError t)))
    (HighamBench.p20OmittedWordTail run t)
```

### D065: `HighamBench.p20InputUnderflowContribution`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `23680fa4dc54682210dfff756a0c9c80d438f1434c13b012471339d1344d0767`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (data : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} {run} data t =>
  instHSub.hSub (Matrix.neg.neg (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (data.AInputUnderflowError t) run.B))
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A (data.BInputUnderflowError t))
```

### D066: `HighamBench.p20IsPowerOfTwo`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D067: `HighamBench.p20RetainedWordPairs`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `c8eb3bb88b390d5375a9471b422e3090d5bc32cb7df3a80bd86cf45656a76a86`

Type:

```lean
(p : Nat) → List (Prod (Fin p) (Fin p))
```

Fully explicit type:

```lean
(p : Nat) → List.{0} (Prod.{0, 0} (Fin p) (Fin p))
```

Definition body (one-level semantic boundary):

```lean
fun p =>
  (List.ofFn fun i =>
      List.filter (fun pair => Decidable.decide (instLTNat.lt (instHAdd.hAdd pair.fst.val pair.snd.val) p))
        (List.ofFn fun j => { fst := i, snd := j })).flatten
```

### D068: `HighamBench.P20MultiwordErrorData.AInputRoundingError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `77508b759f619eaae6ea59e70225de84e49118a884b081fb84ab5cd0565e09fe`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.1
```

### D069: `HighamBench.P20MultiwordErrorData.AInputUnderflowError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `a61f4629a9dc3e36d4d9922d3cdf5d0d19939d2320fda0b4dd53009663de7db5`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.2
```

### D070: `HighamBench.P20MultiwordErrorData.BInputRoundingError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `3148ea52a944bc6c708ad4f36c9ec9299dae022f4c35e5898f4301fa9602ad8f`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.3
```

### D071: `HighamBench.P20MultiwordErrorData.BInputUnderflowError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `986caad039e54caadbcb261d8d5e4a001f2fb4c1d3e06fee37afc7158dc6f13b`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.4
```

### D072: `HighamBench.P20MultiwordErrorData.accumulationRoundingError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `94bc4af35e652c5db0ece164b3de9a930f0c1c154d1df5f01966f14521f16fb9`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.5
```

### D073: `HighamBench.P20MultiwordErrorData.accumulationUnderflowError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `6`
- Semantic SHA-256: `8197ae91b9f748902f96dd3096d37d4e54cfc620084fff0475ef8d99a0155531`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      HighamBench.P20MultiwordErrorData run → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (self : @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run) → ι → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι run self => self.6
```

### D074: `HighamBench.P20MultiwordErrorData.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `6490dacf58d2a01412ef7b0d809ec154a7849d9759bb0edae521b71e0353f66e`

Type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun m n q p ι} →
      (AInputRoundingError AInputUnderflowError : ι → HighamBench.P20Matrix m n) →
        (BInputRoundingError BInputUnderflowError : ι → HighamBench.P20Matrix n q) →
          (accumulationRoundingError accumulationUnderflowError : ι → HighamBench.P20Matrix m q) →
            (∀ (t : ι),
                Eq run.A
                  (instHAdd.hAdd (instHAdd.hAdd (HighamBench.p20AWordApproximation run t) (AInputRoundingError t))
                    (AInputUnderflowError t))) →
              (∀ (t : ι),
                  Eq run.B
                    (instHAdd.hAdd (instHAdd.hAdd (HighamBench.p20BWordApproximation run t) (BInputRoundingError t))
                      (BInputUnderflowError t))) →
                (∀ (t : ι),
                    Eq (HighamBench.p20ExactRetainedWordProduct run t)
                      (instHSub.hSub
                        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p20AWordApproximation run t)
                          (HighamBench.p20BWordApproximation run t))
                        (HighamBench.p20OmittedWordTail run t))) →
                  (∀ (t : ι),
                      Eq (run.computed t)
                        (instHAdd.hAdd
                          (instHAdd.hAdd (HighamBench.p20ExactRetainedWordProduct run t) (accumulationRoundingError t))
                          (accumulationUnderflowError t))) →
                    (∀ (t : ι), Eq (run.model.inputDelta t) 0 → Eq (AInputRoundingError t) 0) →
                      (∀ (t : ι), Eq (run.model.inputDelta t) 0 → Eq (BInputRoundingError t) 0) →
                        (∀ (t : ι), Eq (run.model.inputEta t) 0 → Eq (AInputUnderflowError t) 0) →
                          (∀ (t : ι), Eq (run.model.inputEta t) 0 → Eq (BInputUnderflowError t) 0) →
                            (∀ (t : ι), Eq (run.model.accumulationDelta t) 0 → Eq (accumulationRoundingError t) 0) →
                              (∀ (t : ι), Eq (run.model.accumulationEta t) 0 → Eq (accumulationUnderflowError t) 0) →
                                HighamBench.P20MultiwordErrorData run
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} →
    {run : HighamBench.P20MultiwordRun.{u_1} m n q p ι} →
      (AInputRoundingError AInputUnderflowError : ι → HighamBench.P20Matrix m n) →
        (BInputRoundingError BInputUnderflowError : ι → HighamBench.P20Matrix n q) →
          (accumulationRoundingError accumulationUnderflowError : ι → HighamBench.P20Matrix m q) →
            (A_decomposition :
                ∀ (t : ι),
                  @Eq.{1} (HighamBench.P20Matrix m n) (@HighamBench.P20MultiwordRun.A.{u_1} m n q p ι run)
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix m n) (HighamBench.P20Matrix m n)
                      (HighamBench.P20Matrix m n)
                      (@instHAdd.{0} (HighamBench.P20Matrix m n)
                        (@Matrix.add.{0, 0, 0} (Fin m) (Fin n) Real Real.instAdd))
                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix m n) (HighamBench.P20Matrix m n)
                        (HighamBench.P20Matrix m n)
                        (@instHAdd.{0} (HighamBench.P20Matrix m n)
                          (@Matrix.add.{0, 0, 0} (Fin m) (Fin n) Real Real.instAdd))
                        (@HighamBench.p20AWordApproximation.{u_1} m n q p ι run t) (AInputRoundingError t))
                      (AInputUnderflowError t))) →
              (B_decomposition :
                  ∀ (t : ι),
                    @Eq.{1} (HighamBench.P20Matrix n q) (@HighamBench.P20MultiwordRun.B.{u_1} m n q p ι run)
                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix n q) (HighamBench.P20Matrix n q)
                        (HighamBench.P20Matrix n q)
                        (@instHAdd.{0} (HighamBench.P20Matrix n q)
                          (@Matrix.add.{0, 0, 0} (Fin n) (Fin q) Real Real.instAdd))
                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix n q) (HighamBench.P20Matrix n q)
                          (HighamBench.P20Matrix n q)
                          (@instHAdd.{0} (HighamBench.P20Matrix n q)
                            (@Matrix.add.{0, 0, 0} (Fin n) (Fin q) Real Real.instAdd))
                          (@HighamBench.p20BWordApproximation.{u_1} m n q p ι run t) (BInputRoundingError t))
                        (BInputUnderflowError t))) →
                (retained_partition :
                    ∀ (t : ι),
                      @Eq.{1} (HighamBench.P20Matrix m q)
                        (@HighamBench.p20ExactRetainedWordProduct.{u_1} m n q p ι run t)
                        (@HSub.hSub.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin q) Real) (HighamBench.P20Matrix m q)
                          (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                          (@instHSub.{0} (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                            (@Matrix.sub.{0, 0, 0} (Fin m) (Fin q) Real Real.instSub))
                          (@HMul.hMul.{0, 0, 0} (HighamBench.P20Matrix m n) (HighamBench.P20Matrix n q)
                            (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin q) Real
                              (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                            (@HighamBench.p20AWordApproximation.{u_1} m n q p ι run t)
                            (@HighamBench.p20BWordApproximation.{u_1} m n q p ι run t))
                          (@HighamBench.p20OmittedWordTail.{u_1} m n q p ι run t))) →
                  (accumulation_decomposition :
                      ∀ (t : ι),
                        @Eq.{1} (HighamBench.P20Matrix m q)
                          (@HighamBench.P20MultiwordRun.computed.{u_1} m n q p ι run t)
                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix m q) (HighamBench.P20Matrix m q)
                            (HighamBench.P20Matrix m q)
                            (@instHAdd.{0} (HighamBench.P20Matrix m q)
                              (@Matrix.add.{0, 0, 0} (Fin m) (Fin q) Real Real.instAdd))
                            (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix m q) (HighamBench.P20Matrix m q)
                              (HighamBench.P20Matrix m q)
                              (@instHAdd.{0} (HighamBench.P20Matrix m q)
                                (@Matrix.add.{0, 0, 0} (Fin m) (Fin q) Real Real.instAdd))
                              (@HighamBench.p20ExactRetainedWordProduct.{u_1} m n q p ι run t)
                              (accumulationRoundingError t))
                            (accumulationUnderflowError t))) →
                    (A_rounding_zero :
                        ∀ (t : ι),
                          @Eq.{1} (Real → Real)
                              (@HighamBench.P20Model1.inputDelta.{u_1} ι
                                (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                              (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                (@Zero.toOfNat0.{0} (Real → Real)
                                  (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                    Real.instZero))) →
                            @Eq.{1} (HighamBench.P20Matrix m n) (AInputRoundingError t)
                              (@OfNat.ofNat.{0} (HighamBench.P20Matrix m n) (nat_lit 0)
                                (@Zero.toOfNat0.{0} (HighamBench.P20Matrix m n)
                                  (@Matrix.zero.{0, 0, 0} (Fin m) (Fin n) Real Real.instZero)))) →
                      (B_rounding_zero :
                          ∀ (t : ι),
                            @Eq.{1} (Real → Real)
                                (@HighamBench.P20Model1.inputDelta.{u_1} ι
                                  (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                                (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                  (@Zero.toOfNat0.{0} (Real → Real)
                                    (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                      Real.instZero))) →
                              @Eq.{1} (HighamBench.P20Matrix n q) (BInputRoundingError t)
                                (@OfNat.ofNat.{0} (HighamBench.P20Matrix n q) (nat_lit 0)
                                  (@Zero.toOfNat0.{0} (HighamBench.P20Matrix n q)
                                    (@Matrix.zero.{0, 0, 0} (Fin n) (Fin q) Real Real.instZero)))) →
                        (A_underflow_zero :
                            ∀ (t : ι),
                              @Eq.{1} (Real → Real)
                                  (@HighamBench.P20Model1.inputEta.{u_1} ι
                                    (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                                  (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                    (@Zero.toOfNat0.{0} (Real → Real)
                                      (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                        Real.instZero))) →
                                @Eq.{1} (HighamBench.P20Matrix m n) (AInputUnderflowError t)
                                  (@OfNat.ofNat.{0} (HighamBench.P20Matrix m n) (nat_lit 0)
                                    (@Zero.toOfNat0.{0} (HighamBench.P20Matrix m n)
                                      (@Matrix.zero.{0, 0, 0} (Fin m) (Fin n) Real Real.instZero)))) →
                          (B_underflow_zero :
                              ∀ (t : ι),
                                @Eq.{1} (Real → Real)
                                    (@HighamBench.P20Model1.inputEta.{u_1} ι
                                      (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                                    (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                      (@Zero.toOfNat0.{0} (Real → Real)
                                        (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                          Real.instZero))) →
                                  @Eq.{1} (HighamBench.P20Matrix n q) (BInputUnderflowError t)
                                    (@OfNat.ofNat.{0} (HighamBench.P20Matrix n q) (nat_lit 0)
                                      (@Zero.toOfNat0.{0} (HighamBench.P20Matrix n q)
                                        (@Matrix.zero.{0, 0, 0} (Fin n) (Fin q) Real Real.instZero)))) →
                            (accumulation_rounding_zero :
                                ∀ (t : ι),
                                  @Eq.{1} (Real → Real)
                                      (@HighamBench.P20Model1.accumulationDelta.{u_1} ι
                                        (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                                      (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                        (@Zero.toOfNat0.{0} (Real → Real)
                                          (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                            Real.instZero))) →
                                    @Eq.{1} (HighamBench.P20Matrix m q) (accumulationRoundingError t)
                                      (@OfNat.ofNat.{0} (HighamBench.P20Matrix m q) (nat_lit 0)
                                        (@Zero.toOfNat0.{0} (HighamBench.P20Matrix m q)
                                          (@Matrix.zero.{0, 0, 0} (Fin m) (Fin q) Real Real.instZero)))) →
                              (accumulation_underflow_zero :
                                  ∀ (t : ι),
                                    @Eq.{1} (Real → Real)
                                        (@HighamBench.P20Model1.accumulationEta.{u_1} ι
                                          (@HighamBench.P20MultiwordRun.model.{u_1} m n q p ι run) t)
                                        (@OfNat.ofNat.{0} (Real → Real) (nat_lit 0)
                                          (@Zero.toOfNat0.{0} (Real → Real)
                                            (@Pi.instZero.{0, 0} Real (fun (a : Real) => Real) fun (i : Real) =>
                                              Real.instZero))) →
                                      @Eq.{1} (HighamBench.P20Matrix m q) (accumulationUnderflowError t)
                                        (@OfNat.ofNat.{0} (HighamBench.P20Matrix m q) (nat_lit 0)
                                          (@Zero.toOfNat0.{0} (HighamBench.P20Matrix m q)
                                            (@Matrix.zero.{0, 0, 0} (Fin m) (Fin q) Real Real.instZero)))) →
                                @HighamBench.P20MultiwordErrorData.{u_1} m n q p ι run
```

### D075: `HighamBench.p20OmittedWordTail`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `4d9bd635c661a68662b265b35b679d489fee3096f3a567eef30ea971783dc6c6`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  HighamBench.p20UnscaleProduct (run.rowScale t) (run.columnScale t) fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLENat.le p (instHAdd.hAdd i.val j.val)) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword t i) (run.Bword t j) row col)
```

### D076: `HighamBench.P20Model1.accumulationDelta`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `78f4fa8a808072352b394fd23b9f8e8213dc294f12981f044ac6ab34e63f868c`

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
fun ι self => self.13
```

### D077: `HighamBench.P20Model1.accumulationEta`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c1017184d4654028a07a2d635b6c25c17aea82ef8011778d7ca8ece37cd6d2f0`

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
fun ι self => self.14
```

### D078: `HighamBench.P20Model1.inputDelta`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `f498dd6b9fa820e7e8575e8d39f782b61f9629b97c26b937f83145861b044bdf`

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
fun ι self => self.6
```

### D079: `HighamBench.P20Model1.inputEta`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `42ff47cd7311e65a9520c6de941b31a10d25534aaeb2eefac65de17dea1dfb4f`

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
fun ι self => self.7
```

### D080: `HighamBench.P20MultiwordRun.Aword`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `955e28b1a74a7b1d2337d62173bba50082092918c6f69114404a9197342b4e38`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Fin p → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → Fin p → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.12
```

### D081: `HighamBench.P20MultiwordRun.Bword`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `86205166fbe9973a011490dc58c14dfe34f43d0c59be47c8a5cdede35764b166`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Fin p → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → Fin p → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.13
```

### D082: `HighamBench.P20MultiwordRun.columnScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `e943c5522e2181584d374eed5f1f68372ff9a03e63da8968753625d60a536c82`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Fin q → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → Fin q → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.7
```

### D083: `HighamBench.P20MultiwordRun.rowScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c4ac152ad2707c77d2664ff4cbb7c828f10a598459c0d6cfb6f829e3448e3b42`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → Fin m → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → {ι : Type u_1} → (self : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → ι → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p ι self => self.6
```

### D084: `HighamBench.p20AWordApproximation`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `a91a45911fa9d17d856c58ea58f8b198d7dee535b9496955317ce217830221ef`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → (t : ι) → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t row col =>
  instHMul.hMul (Real.instInv.inv (run.rowScale t row))
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) i.val) (run.Aword t i row col))
```

### D085: `HighamBench.p20BWordApproximation`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `83e23877a59369c44c679f56e678d6f959a9eab93e14bd4aded91115aff6b9b2`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → (t : ι) → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t row col =>
  instHMul.hMul
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) i.val) (run.Bword t i row col))
    (Real.instInv.inv (run.columnScale t col))
```

### D086: `HighamBench.p20ExactRetainedWordProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `89d185a8a35e95ba036183b88c5f925f1714951f417cbeb61ee7b07a1ea15198`

Type:

```lean
{m n q p : Nat} → {ι : Type u_1} → HighamBench.P20MultiwordRun m n q p ι → ι → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  {ι : Type u_1} → (run : HighamBench.P20MultiwordRun.{u_1} m n q p ι) → (t : ι) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} {ι} run t =>
  HighamBench.p20UnscaleProduct (run.rowScale t) (run.columnScale t) fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLTNat.lt (instHAdd.hAdd i.val j.val) p) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (HighamBench.p20InputUnitRoundoff run.model t) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword t i) (run.Bword t j) row col)
```

### D087: `And`

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

### D088: `Eq`

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

### D089: `Filter`

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

### D090: `Filter.NeBot`

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

### D091: `HAdd.hAdd`

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

### D092: `Nat`

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

### D093: `Real`

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

### D094: `Real.instAdd`

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

### D095: `instHAdd`

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

### D096: `Exists`

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

### D097: `Filter.Eventually`

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

### D098: `Fin`

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

### D099: `Fin.fintype`

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

### D100: `HMul.hMul`

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

### D101: `HPow.hPow`

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

### D102: `HSub.hSub`

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

### D103: `Inv.inv`

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

### D104: `LE.le`

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

### D105: `Matrix`

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

### D106: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8eecda35a630fe4097c6149154c07645e87eaf089a78dde5ca01f180806c2a40`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} → [Fintype m] → [Mul α] → [AddCommMonoid α] → HMul (Matrix l m α) (Matrix m n α) (Matrix l n α)
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} →
        [Fintype.{u_2} m] →
          [Mul.{v} α] →
            [AddCommMonoid.{v} α] →
              HMul.{max (max v u_2) u_1, max (max v u_3) u_2, max (max v u_3) u_1} (Matrix.{u_1, u_2, v} l m α)
                (Matrix.{u_2, u_3, v} m n α) (Matrix.{u_1, u_3, v} l n α)
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {α} [Fintype m] [Mul α] [AddCommMonoid α] =>
  { hMul := fun M N i k => dotProduct (fun j => M i j) fun j => N j k }
```

### D107: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D108: `Monoid.toNatPow`

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

### D109: `Nat.cast`

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

### D110: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D111: `One.toOfNat1`

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

### D112: `Real.instAddCommMonoid`

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

### D113: `Real.instAddGroup`

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

### D114: `Real.instInv`

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

### D115: `Real.instLE`

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

### D116: `Real.instMonoid`

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

### D117: `Real.instMul`

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

### D118: `Real.instNatCast`

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

### D119: `Real.instOne`

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

### D120: `Real.instSub`

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

### D121: `Real.lattice`

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

### D122: `abs`

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

### D123: `instHMul`

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

### D124: `instHPow`

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

### D125: `instHSub`

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

### D126: `instOfNatAtLeastTwo`

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

### D127: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D128: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D129: `Asymptotics.IsBigO`

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

### D130: `ConditionallyCompleteLinearOrderBot.toOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.ConditionallyCompleteLattice.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D131: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D132: `Finset.sum`

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

### D133: `Finset.sup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Lattice.Fold`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D134: `Finset.univ`

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

### D135: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D136: `Min.min`

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

### D137: `NNNorm.nnnorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d92a89505c36ed94d23caf93bebbba99b3bc81e96467197a528bee9e0eba28a5`

Type:

```lean
{E : Type u_8} → [self : NNNorm E] → E → NNReal
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NNNorm.{u_8} E] → E → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NNNorm E] => self.1
```

### D138: `NNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D139: `NNReal.instConditionallyCompleteLinearOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D140: `NNReal.toReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D141: `Nat.AtLeastTwo`

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

### D142: `NonAssocSemiring.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `1674e66231d0f66dfe9fae191c7ae33207a78635bcf5490a9cfbb402d16f9bc0`

Type:

```lean
{α : Type u} → [self : NonAssocSemiring α] → NonUnitalNonAssocSemiring α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonAssocSemiring.{u} α] → NonUnitalNonAssocSemiring.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonAssocSemiring α] => self.1
```

### D143: `NonUnitalNonAssocSemiring.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fc6b0a41257a855dbb5b09cfe7e3150884caf2b0f898b30e688420784d3b6e76`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → AddCommMonoid α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring.{u} α] → AddCommMonoid.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocSemiring α] => self.1
```

### D144: `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c697ff5e735ebe18733e51950717037e73ba73e94ac2e99953bfb521708cabd2`

Type:

```lean
{α : Type u_5} → [self : NonUnitalSeminormedCommRing α] → NonUnitalSeminormedRing α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : NonUnitalSeminormedCommRing.{u_5} α] → NonUnitalSeminormedRing.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalSeminormedCommRing α] => self.1
```

### D145: `NonUnitalSeminormedRing.toSeminormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `db7996fa414ad67340b9d6991cd145ac2a5d251a870097d20f2f63e371fb101d`

Type:

```lean
{α : Type u_2} → [NonUnitalSeminormedRing α] → SeminormedAddCommGroup α
```

Fully explicit type:

```lean
{α : Type u_2} → [NonUnitalSeminormedRing.{u_2} α] → SeminormedAddCommGroup.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : NonUnitalSeminormedRing α] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddCommGroup := __src.toAddCommGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D146: `NormedCommRing.toSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ad504b2606febc5a066d58ac540c9826bd1b7fce734d59a7fef63c7c27112fe3`

Type:

```lean
{α : Type u_2} → [β : NormedCommRing α] → SeminormedCommRing α
```

Fully explicit type:

```lean
{α : Type u_2} → [β : NormedCommRing.{u_2} α] → SeminormedCommRing.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : NormedCommRing α] =>
  { toNorm := β.toNorm, toRing := β.toRing, toPseudoMetricSpace := β.toPseudoMetricSpace, dist_eq := ⋯,
    norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D147: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D148: `Real.instMin`

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

### D149: `Real.norm`

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

### D150: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `69cccc1e864661e103785f4a2712b9ad164d845c03b7737801c37e5ac852bad7`

Type:

```lean
NormedCommRing Real
```

Fully explicit type:

```lean
NormedCommRing.{0} Real
```

Definition body (one-level semantic boundary):

```lean
let __src := Real.normedAddCommGroup;
let __src_1 := Real.commRing;
{ toNorm := __src.toNorm, toAddMonoid := __src.toAddMonoid, add_comm := Real.normedCommRing._proof_1,
  toMul := __src_1.toMul, left_distrib := Real.normedCommRing._proof_2, right_distrib := Real.normedCommRing._proof_3,
  zero_mul := Real.normedCommRing._proof_4, mul_zero := Real.normedCommRing._proof_5,
  mul_assoc := Real.normedCommRing._proof_6, toOne := __src_1.toOne, one_mul := Real.normedCommRing._proof_7,
  mul_one := Real.normedCommRing._proof_8, toNatCast := __src_1.toNatCast, natCast_zero := Real.normedCommRing._proof_9,
  natCast_succ := Real.normedCommRing._proof_10, npow := __src_1.npow, npow_zero := Real.normedCommRing._proof_11,
  npow_succ := Real.normedCommRing._proof_12, toNeg := __src.toNeg, toSub := __src.toSub,
  sub_eq_add_neg := Real.normedCommRing._proof_13, zsmul := __src.zsmul, zsmul_zero' := Real.normedCommRing._proof_14,
  zsmul_succ' := Real.normedCommRing._proof_15, zsmul_neg' := Real.normedCommRing._proof_16,
  neg_add_cancel := Real.normedCommRing._proof_17, toIntCast := __src_1.toIntCast,
  intCast_ofNat := Real.normedCommRing._proof_18, intCast_negSucc := Real.normedCommRing._proof_19,
  toMetricSpace := __src.toMetricSpace, dist_eq := ⋯, norm_mul_le := Real.normedCommRing._proof_20, mul_comm := ⋯ }
```

### D151: `Real.sqrt`

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

### D152: `SeminormedAddCommGroup.toSeminormedAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8cf35215f509cdee10a3a95158cbaadd3c5fb584bc0d1f4fad6ecfc69b1bd205`

Type:

```lean
{E : Type u_5} → [SeminormedAddCommGroup E] → SeminormedAddGroup E
```

Fully explicit type:

```lean
{E : Type u_5} → [SeminormedAddCommGroup.{u_5} E] → SeminormedAddGroup.{u_5} E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : SeminormedAddCommGroup E] =>
  have __src := inst;
  { toNorm := __src.toNorm, toAddGroup := __src.toAddGroup, toPseudoMetricSpace := __src.toPseudoMetricSpace,
    dist_eq := ⋯ }
```

### D153: `SeminormedAddGroup.toNNNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `00d678445c0040ace90f6c4fb7b4afa2098bf365a8f75ab815ec0e6e446166c9`

Type:

```lean
{E : Type u_5} → [SeminormedAddGroup E] → NNNorm E
```

Fully explicit type:

```lean
{E : Type u_5} → [SeminormedAddGroup.{u_5} E] → NNNorm.{u_5} E
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : SeminormedAddGroup E] => { nnnorm := fun a => ⟨inst.norm a, ⋯⟩ }
```

### D154: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a29f0377c9baf2265c34aaf85b852e7c4260b34d2dc04574484c335ebc09a6e9`

Type:

```lean
{α : Type u_2} → [β : SeminormedCommRing α] → NonUnitalSeminormedCommRing α
```

Fully explicit type:

```lean
{α : Type u_2} → [β : SeminormedCommRing.{u_2} α] → NonUnitalSeminormedCommRing.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : SeminormedCommRing α] =>
  { toNorm := β.toNorm, toAddMonoid := β.toAddMonoid, toNeg := β.toNeg, toSub := β.toSub, sub_eq_add_neg := ⋯,
    zsmul := β.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯,
    toMul := β.toMul, left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    toPseudoMetricSpace := β.toPseudoMetricSpace, dist_eq := ⋯, norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D155: `Semiring.toNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `33076e5ce1b65d0dacdacdea942f424abbe54f3ff639c158f37c0f533984f227`

Type:

```lean
{α : Type u} → [self : Semiring α] → NonAssocSemiring α
```

Fully explicit type:

```lean
{α : Type u} → [self : Semiring.{u} α] → NonAssocSemiring.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toNonUnitalNonAssocSemiring := self.toNonUnitalNonAssocSemiring, toOne := self.toOne, one_mul := ⋯, mul_one := ⋯,
    toNatCast := self.toNatCast, natCast_zero := ⋯, natCast_succ := ⋯ }
```

### D156: `instAddNat`

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

### D157: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D158: `instSemilatticeSupNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D159: `instSemiringNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `3e4e8247feefdb8229f2843910b9a5df0fb872cbeba12353f5c00b1549c1f2b5`

Type:

```lean
Semiring NNReal
```

Fully explicit type:

```lean
Semiring.{0} NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.semiring
```

### D160: `Bool`

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

### D161: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D162: `Fin.val`

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

### D163: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D164: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D165: `Int.instLEInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D166: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D167: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D168: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D169: `Unit`

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

### D170: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D171: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D172: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D173: `Bool.casesOn`

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

### D174: `Bool.false`

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

### D175: `Bool.true`

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

### D176: `List.foldl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `528cbed637e4ef546b621011d5cf13a5a950202dac919ee6cff2046010954d44`

Type:

```lean
{α : Type u} → {β : Type v} → (α → β → α) → α → List β → α
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (f : α → β → α) → (init : α) → List.{v} β → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f x x_1 =>
  List.brecOn (motive := fun x => α → α) x_1
    (fun x f_1 x_2 =>
      List.foldl.match_1 (fun x x_3 => List.below (motive := fun x => α → α) x_3 → α) x_2 x (fun a x => a)
        (fun a b l x => x.1 (f a b)) f_1)
    x
```

### D177: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D178: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D179: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `31dfcc70f250d68311839281cfb552859ef6a5cdd31e725091d6a2a2f7fb2165`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D180: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a70aebf9da319c4b02023421b33923182c4d5164c2087035016589b80ed1191a`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D181: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D182: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D183: `Unit.unit`

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

### D184: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ff90c894e4369b89945915c4c814dd76d90e450369a804cfc4139fada64048b2`

Type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Fully explicit type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Definition body (one-level semantic boundary):

```lean
fun p [h : Decidable p] => Decidable.casesOn h (fun x => Bool.false) fun x => Bool.true
```

### D185: `List`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `ec06a72bb009eecaedd9dbf6a3349bbea0bbc480e0a21179f4e21b3e219b952d`

Type:

```lean
Type u → Type u
```

Fully explicit type:

```lean
(α : Type u) → Type u
```

### D186: `List.filter`

- Role: `external-frontier`
- Owner module: `Init.Data.List.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `7975b53fb61d3f95cd66b99d3605c0ab38a30a1671157413ddc2342c3a8bd440`

Type:

```lean
{α : Type u} → (α → Bool) → List α → List α
```

Fully explicit type:

```lean
{α : Type u} → (p : α → Bool) → (l : List.{u} α) → List.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p x =>
  List.brecOn x fun x f =>
    List.getLast?.match_1 (fun x => List.below x → List α) x (fun _ x => List.nil)
      (fun a as x => List.filter.match_1 (fun x => List α) (p a) (fun _ => List.cons a x.1) fun _ => x.1) f
```

### D187: `List.flatten`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `79a988f56f7521caffc6b2f64038b6b22e7bf19e9883f481a7670a16914e2da0`

Type:

```lean
{α : Type u_1} → List (List α) → List α
```

Fully explicit type:

```lean
{α : Type u_1} → List.{u_1} (List.{u_1} α) → List.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} x =>
  List.brecOn x fun x f =>
    List.flatten.match_1 (fun x => List.below x → List α) x (fun _ x => List.nil) (fun l L x => l.append x.1) f
```

### D188: `List.ofFn`

- Role: `external-frontier`
- Owner module: `Init.Data.List.OfFn`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `e54777dd091df49539c6c1473fd1928ad87f9e135ba5940e57702ecd3f83b095`

Type:

```lean
{α : Type u_1} → {n : Nat} → (Fin n → α) → List α
```

Fully explicit type:

```lean
{α : Type u_1} → {n : Nat} → (f : Fin n → α) → List.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} f => Fin.foldr n (fun x1 x2 => List.cons (f x1) x2) List.nil
```

### D189: `Matrix.neg`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `1d4a0647aeb637effb2c6c25b5dbf60fa226065a3bcaf43028e168bc24a216b2`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Neg α] → Neg (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Neg.{v} α] → Neg.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Neg α] => Pi.instNeg
```

### D190: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `6`
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

### D191: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (fst : α) → (snd : β) → Prod.{u, v} α β
```

### D192: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D193: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D194: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D195: `Nat.decLe`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D196: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
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
