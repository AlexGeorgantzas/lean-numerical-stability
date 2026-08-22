# Declaration dossier for P20-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p20_t3_multiword_forward_error
    {m n q p : ℕ} (semantics : P20FirstOrderSemantics) :
    (∀ (run : P20StaticMultiwordRun m n q p),
      P20StaticSection4Derivation semantics run →
        p20FirstOrderLe semantics
          (p20StaticMultiwordForwardError run)
          (p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model))
            run.A run.B)) ∧
      (∀ (run : P20StaticMultiwordRun m n q p),
        P20StaticSection4Derivation semantics run →
          p20FirstOrderLe semantics
            (p20StaticMultiwordForwardError run)
            (p20NormwiseEnvelope
              (p20MultiRangeFreeCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticAccumUnitRoundoff run.model))
              run.A run.B +
            p20NormwiseEnvelope
              (p20MultiInputUnderflowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model))
              run.A run.B +
            p20NormwiseEnvelope
              (p20MultiAccumUnderflowCoefficient n p
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model))
              run.A run.B)) ∧
      (∀ run : P20StaticMultiwordRun m n q p,
        p20MultiInputRoundingCoefficient p
              (p20StaticInputUnitRoundoff run.model) =
            ((((p : ℝ) + 1) / 2) *
                p20StaticInputUnitRoundoff run.model ^ (p - 1)) *
              p20SingleInputRoundingCoefficient
                (p20StaticInputUnitRoundoff run.model) ∧
          (n : ℝ) *
              p20MultiInputUnderflowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model) =
            p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20SingleInputUnderflowCoefficient n
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model))
```

## Elaborated target type

```lean
∀ {m n q p : Nat} (semantics : HighamBench.P20FirstOrderSemantics),
  And
    (∀ (run : HighamBench.P20StaticMultiwordRun m n q p) (a : HighamBench.P20StaticSection4Derivation semantics run),
      HighamBench.p20FirstOrderLe semantics (HighamBench.p20StaticMultiwordForwardError run)
        (HighamBench.p20NormwiseEnvelope
          (HighamBench.p20MultiNarrowCoefficient n p (HighamBench.p20StaticInputUnitRoundoff run.model)
            (HighamBench.p20StaticAccumUnitRoundoff run.model) (HighamBench.p20StaticScalingThreshold n run.model)
            (HighamBench.p20StaticInputUnderflowEnvelope run.model)
            (HighamBench.p20StaticAccumUnderflowEnvelope run.model))
          run.A run.B))
    (And
      (∀ (run : HighamBench.P20StaticMultiwordRun m n q p) (a : HighamBench.P20StaticSection4Derivation semantics run),
        HighamBench.p20FirstOrderLe semantics (HighamBench.p20StaticMultiwordForwardError run)
          (instHAdd.hAdd
            (instHAdd.hAdd
              (HighamBench.p20NormwiseEnvelope
                (HighamBench.p20MultiRangeFreeCoefficient n p (HighamBench.p20StaticInputUnitRoundoff run.model)
                  (HighamBench.p20StaticAccumUnitRoundoff run.model))
                run.A run.B)
              (HighamBench.p20NormwiseEnvelope
                (HighamBench.p20MultiInputUnderflowCoefficient n p (HighamBench.p20StaticInputUnitRoundoff run.model)
                  (HighamBench.p20StaticScalingThreshold n run.model)
                  (HighamBench.p20StaticInputUnderflowEnvelope run.model))
                run.A run.B))
            (HighamBench.p20NormwiseEnvelope
              (HighamBench.p20MultiAccumUnderflowCoefficient n p (HighamBench.p20StaticScalingThreshold n run.model)
                (HighamBench.p20StaticAccumUnderflowEnvelope run.model))
              run.A run.B)))
      (∀ (run : HighamBench.P20StaticMultiwordRun m n q p),
        And
          (Eq (HighamBench.p20MultiInputRoundingCoefficient p (HighamBench.p20StaticInputUnitRoundoff run.model))
            (instHMul.hMul
              (instHMul.hMul (instHDiv.hDiv (instHAdd.hAdd p.cast 1) 2)
                (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) (instHSub.hSub p 1)))
              (HighamBench.p20SingleInputRoundingCoefficient (HighamBench.p20StaticInputUnitRoundoff run.model))))
          (Eq
            (instHMul.hMul n.cast
              (HighamBench.p20MultiInputUnderflowCoefficient n p (HighamBench.p20StaticInputUnitRoundoff run.model)
                (HighamBench.p20StaticScalingThreshold n run.model)
                (HighamBench.p20StaticInputUnderflowEnvelope run.model)))
            (instHMul.hMul (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) (instHSub.hSub p 1))
              (HighamBench.p20SingleInputUnderflowCoefficient n (HighamBench.p20StaticScalingThreshold n run.model)
                (HighamBench.p20StaticInputUnderflowEnvelope run.model))))))
```

## Fully explicit elaborated target type

```lean
∀ {m n q p : Nat} (semantics : HighamBench.P20FirstOrderSemantics),
  And
    (∀ (run : HighamBench.P20StaticMultiwordRun m n q p)
      (a : @HighamBench.P20StaticSection4Derivation semantics m n q p run),
      HighamBench.p20FirstOrderLe semantics (@HighamBench.p20StaticMultiwordForwardError m n q p run)
        (@HighamBench.p20NormwiseEnvelope m n q
          (HighamBench.p20MultiNarrowCoefficient n p
            (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
            (HighamBench.p20StaticAccumUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
            (HighamBench.p20StaticScalingThreshold n (@HighamBench.P20StaticMultiwordRun.model m n q p run))
            (HighamBench.p20StaticInputUnderflowEnvelope (@HighamBench.P20StaticMultiwordRun.model m n q p run))
            (HighamBench.p20StaticAccumUnderflowEnvelope (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
          (@HighamBench.P20StaticMultiwordRun.A m n q p run) (@HighamBench.P20StaticMultiwordRun.B m n q p run)))
    (And
      (∀ (run : HighamBench.P20StaticMultiwordRun m n q p)
        (a : @HighamBench.P20StaticSection4Derivation semantics m n q p run),
        HighamBench.p20FirstOrderLe semantics (@HighamBench.p20StaticMultiwordForwardError m n q p run)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HighamBench.p20NormwiseEnvelope m n q
                (HighamBench.p20MultiRangeFreeCoefficient n p
                  (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                  (HighamBench.p20StaticAccumUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
                (@HighamBench.P20StaticMultiwordRun.A m n q p run) (@HighamBench.P20StaticMultiwordRun.B m n q p run))
              (@HighamBench.p20NormwiseEnvelope m n q
                (HighamBench.p20MultiInputUnderflowCoefficient n p
                  (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                  (HighamBench.p20StaticScalingThreshold n (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                  (HighamBench.p20StaticInputUnderflowEnvelope (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
                (@HighamBench.P20StaticMultiwordRun.A m n q p run) (@HighamBench.P20StaticMultiwordRun.B m n q p run)))
            (@HighamBench.p20NormwiseEnvelope m n q
              (HighamBench.p20MultiAccumUnderflowCoefficient n p
                (HighamBench.p20StaticScalingThreshold n (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                (HighamBench.p20StaticAccumUnderflowEnvelope (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
              (@HighamBench.P20StaticMultiwordRun.A m n q p run) (@HighamBench.P20StaticMultiwordRun.B m n q p run))))
      (∀ (run : HighamBench.P20StaticMultiwordRun m n q p),
        And
          (@Eq.{1} Real
            (HighamBench.p20MultiInputRoundingCoefficient p
              (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@Nat.cast.{0} Real Real.instNatCast p)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                  (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (HighamBench.p20SingleInputRoundingCoefficient
                (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run)))))
          (@Eq.{1} Real
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast n)
              (HighamBench.p20MultiInputUnderflowCoefficient n p
                (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                (HighamBench.p20StaticScalingThreshold n (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                (HighamBench.p20StaticInputUnderflowEnvelope (@HighamBench.P20StaticMultiwordRun.model m n q p run))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (HighamBench.p20StaticInputUnitRoundoff (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) p
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (HighamBench.p20SingleInputUnderflowCoefficient n
                (HighamBench.p20StaticScalingThreshold n (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                (HighamBench.p20StaticInputUnderflowEnvelope
                  (@HighamBench.P20StaticMultiwordRun.model m n q p run)))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P20Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P20Definitions` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Real.Sqrt`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P20FirstOrderSemantics`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `f2edb688bf24107f4483f8ca3f1a4c1ac22236239f0226d7fabb02affe19d395`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D002: `HighamBench.P20StaticMultiwordRun`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ba24be371c312a770cc2b9d6fd08a425e600865f5a9f40e91367d729d2a6f04d`

Type:

```lean
Nat → Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(m n q p : Nat) → Type
```

### D003: `HighamBench.P20StaticMultiwordRun.A`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `468c1a38250f5e60d7883041a0cbef728dfedb248c87c34cca63c2033277fa24`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.4
```

### D004: `HighamBench.P20StaticMultiwordRun.B`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fed5b57c9fbe3546a82db9ae27bd3c26be244d7edb4852f05d169347aad35e5e`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.5
```

### D005: `HighamBench.P20StaticMultiwordRun.model`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `1d0362498066d9e568122beb1d2a6d5af0732f3fd5dd4209d47c6d950f972e62`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20StaticNearestModel1
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20StaticNearestModel1
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.3
```

### D006: `HighamBench.P20StaticSection4Derivation`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `8ef8b26342c5a67d4f35c4ac66d27832a84297dcf2c71741a07e32cf87dc8b3b`

Type:

```lean
HighamBench.P20FirstOrderSemantics → {m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Type
```

Fully explicit type:

```lean
(semantics : HighamBench.P20FirstOrderSemantics) →
  {m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → Type
```

### D007: `HighamBench.p20FirstOrderLe`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fb2df0faeee47322d20b7cfbcb1484bf8c5ddf88de1becb7ebd3211db8b053bd`

Type:

```lean
HighamBench.P20FirstOrderSemantics → Real → Real → Prop
```

Fully explicit type:

```lean
(semantics : HighamBench.P20FirstOrderSemantics) → (lhs rhs : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun semantics lhs rhs =>
  Exists fun remainder => And (semantics.secondOrder remainder) (Real.instLE.le lhs (instHAdd.hAdd rhs (abs remainder)))
```

### D008: `HighamBench.p20MultiAccumUnderflowCoefficient`

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

### D009: `HighamBench.p20MultiInputRoundingCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D010: `HighamBench.p20MultiInputUnderflowCoefficient`

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

### D011: `HighamBench.p20MultiNarrowCoefficient`

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

### D012: `HighamBench.p20MultiRangeFreeCoefficient`

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

### D013: `HighamBench.p20NormwiseEnvelope`

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

### D014: `HighamBench.p20SingleInputRoundingCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9c60932f99879417bbf4517e3809066d375e41a167b91753ac7404ac9a619df3`

Type:

```lean
Real → Real
```

Fully explicit type:

```lean
(u : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun u => instHMul.hMul 2 u
```

### D015: `HighamBench.p20SingleInputUnderflowCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d4d5db82952e69b8eba75f6811724b53957dd863e22ba7f23efe5369e4ed612e`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (theta gmin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n theta gmin =>
  instHMul.hMul (instHMul.hMul (instHMul.hMul 4 (instHPow.hPow n.cast 2)) (Real.instInv.inv theta)) gmin
```

### D016: `HighamBench.p20StaticAccumUnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `be59dd8ef1d970cdf9b759f6bc31124ac4ee2464b0025c399e48a3512e04b761`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real
```

Fully explicit type:

```lean
(model : HighamBench.P20StaticNearestModel1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model =>
  HighamBench.p20UnderflowEnvelope model.accumulationFormat.precision model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals
```

### D017: `HighamBench.p20StaticAccumUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1f2d201bc9ea329e579ca2571abbb2c506bc0fc8c168b258ceed88c1f7d26d2f`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real
```

Fully explicit type:

```lean
(model : HighamBench.P20StaticNearestModel1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model => HighamBench.p20UnitRoundoff model.accumulationFormat.precision
```

### D018: `HighamBench.p20StaticInputUnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3150ac4d77a8896c28b5d82da04e0c317811db9b9f0fb3d0b459e6b9c10df986`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real
```

Fully explicit type:

```lean
(model : HighamBench.P20StaticNearestModel1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model =>
  HighamBench.p20UnderflowEnvelope model.inputFormat.precision model.inputFormat.minExponent
    model.inputFormat.hasSubnormals
```

### D019: `HighamBench.p20StaticInputUnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `80ddb95b2d83a1884156016c43f22b53918369613f62170602658999d2457bac`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real
```

Fully explicit type:

```lean
(model : HighamBench.P20StaticNearestModel1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun model => HighamBench.p20UnitRoundoff model.inputFormat.precision
```

### D020: `HighamBench.p20StaticMultiwordForwardError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b552ced0f8096390c09f6d0f5081d946ed8484615c8d5203b392d9ece7e640ec`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  HighamBench.p20InfNormRect
    (instHSub.hSub run.computed (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul run.A run.B))
```

### D021: `HighamBench.p20StaticScalingThreshold`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5954e08cdcea5205c005bfb0dfd5fec31ca5598f313e185555f7586e60a4b286`

Type:

```lean
Nat → HighamBench.P20StaticNearestModel1 → Real
```

Fully explicit type:

```lean
(n : Nat) → (model : HighamBench.P20StaticNearestModel1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n model =>
  HighamBench.p20ScalingThreshold n (HighamBench.p20MaxFinite model.inputFormat.precision model.inputFormat.maxExponent)
    (HighamBench.p20MaxFinite model.accumulationFormat.precision model.accumulationFormat.maxExponent)
```

### D022: `HighamBench.P20FirstOrderSemantics.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `dbf09d0197efd4fe3f1be1c3f41753166e84f54c3537c5d7364e0a21e1d9f270`

Type:

```lean
(secondOrder : Real → Prop) →
  secondOrder 0 →
    (∀ {x y : Real}, secondOrder x → secondOrder y → secondOrder (instHAdd.hAdd x y)) →
      (∀ {x : Real}, secondOrder x → secondOrder (abs x)) → HighamBench.P20FirstOrderSemantics
```

Fully explicit type:

```lean
(secondOrder : Real → Prop) →
  (zero_secondOrder : secondOrder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
    (add_secondOrder :
        ∀ {x y : Real},
          secondOrder x →
            secondOrder y → secondOrder (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)) →
      (abs_secondOrder : ∀ {x : Real}, secondOrder x → secondOrder (@abs.{0} Real Real.lattice Real.instAddGroup x)) →
        HighamBench.P20FirstOrderSemantics
```

### D023: `HighamBench.P20FirstOrderSemantics.secondOrder`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `90968f60e8ad6d3748a0e2bfbd73b1389fd62502d40766d62f235ae7d5eb02e9`

Type:

```lean
HighamBench.P20FirstOrderSemantics → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P20FirstOrderSemantics) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D024: `HighamBench.P20Matrix`

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

### D025: `HighamBench.P20StaticBinaryFormat.hasSubnormals`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `12d262b8446cf7c6c47cb88687060cc62a00722a9508d327962a662efd9fa79e`

Type:

```lean
HighamBench.P20StaticBinaryFormat → Bool
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticBinaryFormat) → Bool
```

Definition body (one-level semantic boundary):

```lean
fun self => self.4
```

### D026: `HighamBench.P20StaticBinaryFormat.maxExponent`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3c88de1e2276413265f331b9b7d8c2e0e4e7b3d4c91dfe03084b3b00515ee6e7`

Type:

```lean
HighamBench.P20StaticBinaryFormat → Int
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticBinaryFormat) → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D027: `HighamBench.P20StaticBinaryFormat.minExponent`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `413ce9de7a00001e543ad2ad3103cdb39776dd2cd71dcee21c387e1520ef9a57`

Type:

```lean
HighamBench.P20StaticBinaryFormat → Int
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticBinaryFormat) → Int
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D028: `HighamBench.P20StaticBinaryFormat.precision`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c756b1b4a4cf8e4c5892149c99b4ad6dafffb8b7aafaaaa18142341087a4c719`

Type:

```lean
HighamBench.P20StaticBinaryFormat → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticBinaryFormat) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D029: `HighamBench.P20StaticMultiwordRun.computed`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2196fbb59e3bffa94526c4b8102e9dc3ef8f6f35b0e8ceaf79b3dbc1df72e541`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.20
```

### D030: `HighamBench.P20StaticMultiwordRun.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e102e7d20abfbe2da70a388f4912adaae5600d0741ad787277ae7769e746cb81`

Type:

```lean
{m n q p : Nat} →
  And (instLTNat.lt 0 m) (And (instLTNat.lt 0 n) (instLTNat.lt 0 q)) →
    instLTNat.lt 0 p →
      (model : HighamBench.P20StaticNearestModel1) →
        (A : HighamBench.P20Matrix m n) →
          (B : HighamBench.P20Matrix n q) →
            (rowScale : Fin m → Real) →
              (columnScale : Fin q → Real) →
                (∀ (i : Fin m),
                    HighamBench.p20MaximalPowerTwoScale (HighamBench.p20StaticScalingThreshold n model)
                      (HighamBench.p20InfNormVec (A i)) (rowScale i)) →
                  (∀ (j : Fin q),
                      HighamBench.p20MaximalPowerTwoScale (HighamBench.p20StaticScalingThreshold n model)
                        (HighamBench.p20InfNormVec fun i => B i j) (columnScale j)) →
                    (∀ (i : Fin m) (j : Fin n),
                        Real.instLE.le (abs (HighamBench.p20ScaleRows rowScale A i j))
                          (HighamBench.p20StaticScalingThreshold n model)) →
                      (∀ (i : Fin n) (j : Fin q),
                          Real.instLE.le (abs (HighamBench.p20ScaleColumns B columnScale i j))
                            (HighamBench.p20StaticScalingThreshold n model)) →
                        (Aword : Fin p → HighamBench.P20Matrix m n) →
                          (Bword : Fin p → HighamBench.P20Matrix n q) →
                            (∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                Eq (Aword i row col)
                                  (model.inputRound
                                    (instHDiv.hDiv
                                      (instHSub.hSub (HighamBench.p20ScaleRows rowScale A row col)
                                        ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                          instHMul.hMul
                                            (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) k.val)
                                            (Aword k row col)))
                                      (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) i.val)))) →
                              (∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                  model.inputNoOverflow
                                    (instHDiv.hDiv
                                      (instHSub.hSub (HighamBench.p20ScaleRows rowScale A row col)
                                        ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum fun k =>
                                          instHMul.hMul
                                            (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) k.val)
                                            (Aword k row col)))
                                      (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) i.val))) →
                                (∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                    Eq (Bword i row col)
                                      (model.inputRound
                                        (instHDiv.hDiv
                                          (instHSub.hSub (HighamBench.p20ScaleColumns B columnScale row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) k.val)
                                                (Bword k row col)))
                                          (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) i.val)))) →
                                  (∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                      model.inputNoOverflow
                                        (instHDiv.hDiv
                                          (instHSub.hSub (HighamBench.p20ScaleColumns B columnScale row col)
                                            ((Finset.filter (fun k => instLTNat.lt k.val i.val) Finset.univ).sum
                                              fun k =>
                                              instHMul.hMul
                                                (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) k.val)
                                                (Bword k row col)))
                                          (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model) i.val))) →
                                    (∀ (i j : Fin p),
                                        instLTNat.lt (instHAdd.hAdd i.val j.val) p →
                                          ∀ (row : Fin m) (col : Fin q),
                                            HighamBench.p20StaticInnerProductNoOverflow model (Aword i row) fun k =>
                                              Bword j k col) →
                                      (∀ (row : Fin m) (col : Fin q),
                                          HighamBench.p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
                                            model.accumulationRound 0
                                            (List.map
                                              (fun pair =>
                                                instHMul.hMul
                                                  (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff model)
                                                    (instHAdd.hAdd pair.fst.val pair.snd.val))
                                                  (HighamBench.p20StaticAccumulatedInnerProduct model
                                                    (Aword pair.fst row) fun k => Bword pair.snd k col))
                                              (HighamBench.p20RetainedWordPairs p))) →
                                        (computed : HighamBench.P20Matrix m q) →
                                          Eq computed
                                              (HighamBench.p20UnscaleProduct rowScale columnScale
                                                (HighamBench.p20StaticRetainedWordProduct model
                                                  (HighamBench.p20StaticInputUnitRoundoff model) Aword Bword)) →
                                            HighamBench.P20StaticMultiwordRun m n q p
```

Fully explicit type:

```lean
{m n q p : Nat} →
  (dimension_pos :
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
        (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q))) →
    (word_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
      (model : HighamBench.P20StaticNearestModel1) →
        (A : HighamBench.P20Matrix m n) →
          (B : HighamBench.P20Matrix n q) →
            (rowScale : Fin m → Real) →
              (columnScale : Fin q → Real) →
                (row_scaling_rule :
                    ∀ (i : Fin m),
                      HighamBench.p20MaximalPowerTwoScale (HighamBench.p20StaticScalingThreshold n model)
                        (@HighamBench.p20InfNormVec n (A i)) (rowScale i)) →
                  (column_scaling_rule :
                      ∀ (j : Fin q),
                        HighamBench.p20MaximalPowerTwoScale (HighamBench.p20StaticScalingThreshold n model)
                          (@HighamBench.p20InfNormVec n fun (i : Fin n) => B i j) (columnScale j)) →
                    (scaled_A_bound :
                        ∀ (i : Fin m) (j : Fin n),
                          @LE.le.{0} Real Real.instLE
                            (@abs.{0} Real Real.lattice Real.instAddGroup
                              (@HighamBench.p20ScaleRows m n rowScale A i j))
                            (HighamBench.p20StaticScalingThreshold n model)) →
                      (scaled_B_bound :
                          ∀ (i : Fin n) (j : Fin q),
                            @LE.le.{0} Real Real.instLE
                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                (@HighamBench.p20ScaleColumns n q B columnScale i j))
                              (HighamBench.p20StaticScalingThreshold n model)) →
                        (Aword : Fin p → HighamBench.P20Matrix m n) →
                          (Bword : Fin p → HighamBench.P20Matrix n q) →
                            (Aword_equation :
                                ∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                  @Eq.{1} Real (Aword i row col)
                                    (HighamBench.P20StaticNearestModel1.inputRound model
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                          (@HighamBench.p20ScaleRows m n rowScale A row col)
                                          (@Finset.sum.{0, 0} (Fin p) Real Real.instAddCommMonoid
                                            (@Finset.filter.{0} (Fin p)
                                              (fun (k : Fin p) =>
                                                @LT.lt.{0} Nat instLTNat (@Fin.val p k) (@Fin.val p i))
                                              (fun (a : Fin p) => Nat.decLt (@Fin.val p a) (@Fin.val p i))
                                              (@Finset.univ.{0} (Fin p) (Fin.fintype p)))
                                            fun (k : Fin p) =>
                                            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p k))
                                              (Aword k row col)))
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                          (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p i))))) →
                              (Aword_no_overflow :
                                  ∀ (i : Fin p) (row : Fin m) (col : Fin n),
                                    HighamBench.P20StaticNearestModel1.inputNoOverflow model
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                          (@HighamBench.p20ScaleRows m n rowScale A row col)
                                          (@Finset.sum.{0, 0} (Fin p) Real Real.instAddCommMonoid
                                            (@Finset.filter.{0} (Fin p)
                                              (fun (k : Fin p) =>
                                                @LT.lt.{0} Nat instLTNat (@Fin.val p k) (@Fin.val p i))
                                              (fun (a : Fin p) => Nat.decLt (@Fin.val p a) (@Fin.val p i))
                                              (@Finset.univ.{0} (Fin p) (Fin.fintype p)))
                                            fun (k : Fin p) =>
                                            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p k))
                                              (Aword k row col)))
                                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                          (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p i)))) →
                                (Bword_equation :
                                    ∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                      @Eq.{1} Real (Bword i row col)
                                        (HighamBench.P20StaticNearestModel1.inputRound model
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@HighamBench.p20ScaleColumns n q B columnScale row col)
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
                                                    (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p k))
                                                  (Bword k row col)))
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                              (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p i))))) →
                                  (Bword_no_overflow :
                                      ∀ (i : Fin p) (row : Fin n) (col : Fin q),
                                        HighamBench.P20StaticNearestModel1.inputNoOverflow model
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@HighamBench.p20ScaleColumns n q B columnScale row col)
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
                                                    (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p k))
                                                  (Bword k row col)))
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                              (HighamBench.p20StaticInputUnitRoundoff model) (@Fin.val p i)))) →
                                    (accumulation_no_overflow :
                                        ∀ (i j : Fin p),
                                          @LT.lt.{0} Nat instLTNat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@Fin.val p i) (@Fin.val p j))
                                              p →
                                            ∀ (row : Fin m) (col : Fin q),
                                              @HighamBench.p20StaticInnerProductNoOverflow n model (Aword i row)
                                                fun (k : Fin n) => Bword j k col) →
                                      (retained_sum_no_overflow :
                                          ∀ (row : Fin m) (col : Fin q),
                                            HighamBench.p20RoundedFoldNoOverflowFrom
                                              (HighamBench.P20StaticNearestModel1.accumulationNoOverflow model)
                                              (HighamBench.P20StaticNearestModel1.accumulationRound model)
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                              (@List.map.{0, 0} (Prod.{0, 0} (Fin p) (Fin p)) Real
                                                (fun (pair : Prod.{0, 0} (Fin p) (Fin p)) =>
                                                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                      (@instHPow.{0, 0} Real Nat
                                                        (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                      (HighamBench.p20StaticInputUnitRoundoff model)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@Fin.val p (@Prod.fst.{0, 0} (Fin p) (Fin p) pair))
                                                        (@Fin.val p (@Prod.snd.{0, 0} (Fin p) (Fin p) pair))))
                                                    (@HighamBench.p20StaticAccumulatedInnerProduct n model
                                                      (Aword (@Prod.fst.{0, 0} (Fin p) (Fin p) pair) row)
                                                      fun (k : Fin n) =>
                                                      Bword (@Prod.snd.{0, 0} (Fin p) (Fin p) pair) k col))
                                                (HighamBench.p20RetainedWordPairs p))) →
                                        (computed : HighamBench.P20Matrix m q) →
                                          (computed_equation :
                                              @Eq.{1} (HighamBench.P20Matrix m q) computed
                                                (@HighamBench.p20UnscaleProduct m q rowScale columnScale
                                                  (@HighamBench.p20StaticRetainedWordProduct m n q p model
                                                    (HighamBench.p20StaticInputUnitRoundoff model) Aword Bword))) →
                                            HighamBench.P20StaticMultiwordRun m n q p
```

### D031: `HighamBench.P20StaticNearestModel1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `6926c389e89ca6de69ecf72b7cc3ec994fee507a58e514b84a256962788d624a`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D032: `HighamBench.P20StaticNearestModel1.accumulationFormat`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9710afba4fc16094d33288533455f23ceb0965aa0c1da86015ff26e74464c33d`

Type:

```lean
HighamBench.P20StaticNearestModel1 → HighamBench.P20StaticBinaryFormat
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → HighamBench.P20StaticBinaryFormat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D033: `HighamBench.P20StaticNearestModel1.inputFormat`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `a58d40257980f41d770cde074cf877dcc7ebc6731c42b3c939d5baea529f07de`

Type:

```lean
HighamBench.P20StaticNearestModel1 → HighamBench.P20StaticBinaryFormat
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → HighamBench.P20StaticBinaryFormat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D034: `HighamBench.P20StaticSection4Derivation.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `e1e4e0e04fecdf93a41d27d76443f5cfdcae65e0e4f365de5bfc15d2cc71b18f`

Type:

```lean
{semantics : HighamBench.P20FirstOrderSemantics} →
  {m n q p : Nat} →
    {run : HighamBench.P20StaticMultiwordRun m n q p} →
      (AError : HighamBench.P20Matrix m n) →
        (BError : HighamBench.P20Matrix n q) →
          Eq run.A (instHAdd.hAdd (HighamBench.p20StaticAWordApproximation run) AError) →
            Eq run.B (instHAdd.hAdd (HighamBench.p20StaticBWordApproximation run) BError) →
              Real.instLE.le (HighamBench.p20InfNormRect AError)
                  (instHMul.hMul (HighamBench.p20StaticZeta run) (HighamBench.p20InfNormRect run.A)) →
                Real.instLE.le (HighamBench.p20InfNormRect BError)
                    (instHMul.hMul (HighamBench.p20StaticZeta run) (HighamBench.p20InfNormRect run.B)) →
                  Eq (HighamBench.p20StaticExactRetainedWordProduct run)
                      (instHSub.hSub
                        (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p20StaticAWordApproximation run)
                          (HighamBench.p20StaticBWordApproximation run))
                        (HighamBench.p20StaticOmittedWordTail run)) →
                    (omittedRemainder : Real) →
                      semantics.secondOrder omittedRemainder →
                        Real.instLE.le (HighamBench.p20InfNormRect (HighamBench.p20StaticOmittedWordTail run))
                            (instHAdd.hAdd
                              (HighamBench.p20NormwiseEnvelope
                                (HighamBench.p20StaticOmittedCoefficient p
                                  (HighamBench.p20StaticInputUnitRoundoff run.model))
                                run.A run.B)
                              (abs omittedRemainder)) →
                          (accumulationRemainder : Real) →
                            semantics.secondOrder accumulationRemainder →
                              (underflowCount : Nat) →
                                Real.instLE.le underflowCount.cast
                                    (instHDiv.hDiv
                                      (instHMul.hMul (instHMul.hMul n.cast p.cast) (instHAdd.hAdd p.cast 1)) 2) →
                                  Real.instLE.le
                                      (HighamBench.p20InfNormRect (HighamBench.p20StaticAccumulationError run))
                                      (instHAdd.hAdd
                                        (HighamBench.p20NormwiseEnvelope
                                          (HighamBench.p20StaticRawAccumulationCoefficient n p underflowCount
                                            (HighamBench.p20StaticAccumUnitRoundoff run.model)
                                            (HighamBench.p20StaticScalingThreshold n run.model)
                                            (HighamBench.p20StaticAccumUnderflowEnvelope run.model))
                                          run.A run.B)
                                        (abs accumulationRemainder)) →
                                    semantics.secondOrder
                                        (instHMul.hMul
                                          (instHMul.hMul (instHPow.hPow (HighamBench.p20StaticZeta run) 2)
                                            (HighamBench.p20InfNormRect run.A))
                                          (HighamBench.p20InfNormRect run.B)) →
                                      HighamBench.P20StaticSection4Derivation semantics run
```

Fully explicit type:

```lean
{semantics : HighamBench.P20FirstOrderSemantics} →
  {m n q p : Nat} →
    {run : HighamBench.P20StaticMultiwordRun m n q p} →
      (AError : HighamBench.P20Matrix m n) →
        (BError : HighamBench.P20Matrix n q) →
          (A_decomposition :
              @Eq.{1} (HighamBench.P20Matrix m n) (@HighamBench.P20StaticMultiwordRun.A m n q p run)
                (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix m n) (HighamBench.P20Matrix m n)
                  (HighamBench.P20Matrix m n)
                  (@instHAdd.{0} (HighamBench.P20Matrix m n) (@Matrix.add.{0, 0, 0} (Fin m) (Fin n) Real Real.instAdd))
                  (@HighamBench.p20StaticAWordApproximation m n q p run) AError)) →
            (B_decomposition :
                @Eq.{1} (HighamBench.P20Matrix n q) (@HighamBench.P20StaticMultiwordRun.B m n q p run)
                  (@HAdd.hAdd.{0, 0, 0} (HighamBench.P20Matrix n q) (HighamBench.P20Matrix n q)
                    (HighamBench.P20Matrix n q)
                    (@instHAdd.{0} (HighamBench.P20Matrix n q)
                      (@Matrix.add.{0, 0, 0} (Fin n) (Fin q) Real Real.instAdd))
                    (@HighamBench.p20StaticBWordApproximation m n q p run) BError)) →
              (A_error_bound :
                  @LE.le.{0} Real Real.instLE (@HighamBench.p20InfNormRect m n AError)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HighamBench.p20StaticZeta m n q p run)
                      (@HighamBench.p20InfNormRect m n (@HighamBench.P20StaticMultiwordRun.A m n q p run)))) →
                (B_error_bound :
                    @LE.le.{0} Real Real.instLE (@HighamBench.p20InfNormRect n q BError)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HighamBench.p20StaticZeta m n q p run)
                        (@HighamBench.p20InfNormRect n q (@HighamBench.P20StaticMultiwordRun.B m n q p run)))) →
                  (retained_partition :
                      @Eq.{1} (HighamBench.P20Matrix m q) (@HighamBench.p20StaticExactRetainedWordProduct m n q p run)
                        (@HSub.hSub.{0, 0, 0} (Matrix.{0, 0, 0} (Fin m) (Fin q) Real) (HighamBench.P20Matrix m q)
                          (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                          (@instHSub.{0} (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                            (@Matrix.sub.{0, 0, 0} (Fin m) (Fin q) Real Real.instSub))
                          (@HMul.hMul.{0, 0, 0} (HighamBench.P20Matrix m n) (HighamBench.P20Matrix n q)
                            (Matrix.{0, 0, 0} (Fin m) (Fin q) Real)
                            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, 0, 0, 0} (Fin m) (Fin n) (Fin q) Real
                              (Fin.fintype n) Real.instMul Real.instAddCommMonoid)
                            (@HighamBench.p20StaticAWordApproximation m n q p run)
                            (@HighamBench.p20StaticBWordApproximation m n q p run))
                          (@HighamBench.p20StaticOmittedWordTail m n q p run))) →
                    (omittedRemainder : Real) →
                      (omitted_remainder_second_order :
                          HighamBench.P20FirstOrderSemantics.secondOrder semantics omittedRemainder) →
                        (omitted_tail_bound :
                            @LE.le.{0} Real Real.instLE
                              (@HighamBench.p20InfNormRect m q (@HighamBench.p20StaticOmittedWordTail m n q p run))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HighamBench.p20NormwiseEnvelope m n q
                                  (HighamBench.p20StaticOmittedCoefficient p
                                    (HighamBench.p20StaticInputUnitRoundoff
                                      (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
                                  (@HighamBench.P20StaticMultiwordRun.A m n q p run)
                                  (@HighamBench.P20StaticMultiwordRun.B m n q p run))
                                (@abs.{0} Real Real.lattice Real.instAddGroup omittedRemainder))) →
                          (accumulationRemainder : Real) →
                            (accumulation_remainder_second_order :
                                HighamBench.P20FirstOrderSemantics.secondOrder semantics accumulationRemainder) →
                              (underflowCount : Nat) →
                                (underflow_count_bound :
                                    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast underflowCount)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@Nat.cast.{0} Real Real.instNatCast n)
                                            (@Nat.cast.{0} Real Real.instNatCast p))
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@Nat.cast.{0} Real Real.instNatCast p)
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))) →
                                  (accumulation_error_bound :
                                      @LE.le.{0} Real Real.instLE
                                        (@HighamBench.p20InfNormRect m q
                                          (@HighamBench.p20StaticAccumulationError m n q p run))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@HighamBench.p20NormwiseEnvelope m n q
                                            (HighamBench.p20StaticRawAccumulationCoefficient n p underflowCount
                                              (HighamBench.p20StaticAccumUnitRoundoff
                                                (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                                              (HighamBench.p20StaticScalingThreshold n
                                                (@HighamBench.P20StaticMultiwordRun.model m n q p run))
                                              (HighamBench.p20StaticAccumUnderflowEnvelope
                                                (@HighamBench.P20StaticMultiwordRun.model m n q p run)))
                                            (@HighamBench.P20StaticMultiwordRun.A m n q p run)
                                            (@HighamBench.P20StaticMultiwordRun.B m n q p run))
                                          (@abs.{0} Real Real.lattice Real.instAddGroup accumulationRemainder))) →
                                    (quadratic_second_order :
                                        HighamBench.P20FirstOrderSemantics.secondOrder semantics
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                (@HighamBench.p20StaticZeta m n q p run)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HighamBench.p20InfNormRect m n
                                                (@HighamBench.P20StaticMultiwordRun.A m n q p run)))
                                            (@HighamBench.p20InfNormRect n q
                                              (@HighamBench.P20StaticMultiwordRun.B m n q p run)))) →
                                      @HighamBench.P20StaticSection4Derivation semantics m n q p run
```

### D035: `HighamBench.p20InfNormRect`

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

### D036: `HighamBench.p20IsPowerOfTwo._proof_1`

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

### D037: `HighamBench.p20MaxFinite`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D038: `HighamBench.p20MultiAccumRoundingCoefficient`

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

### D039: `HighamBench.p20ScalingThreshold`

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

### D040: `HighamBench.p20SingleInputUnderflowBound._proof_1`

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

### D041: `HighamBench.p20UnderflowEnvelope`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D042: `HighamBench.p20UnitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D043: `HighamBench.P20StaticBinaryFormat`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d7413b73a7ad69b98dc5442ebbbdc88576a9ef3d0d454547165fca6c44972bc9`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D044: `HighamBench.P20StaticNearestModel1.accumulationNoOverflow`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `792791a0867cbfa46f9a7bcd3765f1203d4a225c1225c66e1176d42ea3b58e4b`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.18
```

### D045: `HighamBench.P20StaticNearestModel1.accumulationRound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `30ce35c54c896a4931f5255243d743ec3e934999f96f263246c7f00444561ea7`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.15
```

### D046: `HighamBench.P20StaticNearestModel1.inputNoOverflow`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `55b414c88463908661427fe77d14587a93f88c903944710a5ba2422cde1f5bce`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D047: `HighamBench.P20StaticNearestModel1.inputRound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `581ec48f5ff9f0fa3720a20c607b6d4aa2055ef843a6dc3aac38e32b201be5d4`

Type:

```lean
HighamBench.P20StaticNearestModel1 → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P20StaticNearestModel1) → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D048: `HighamBench.P20StaticNearestModel1.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e28717a002a95568b89c776278fcaa0f6885dfbd6cd67f0dbf0a18e27e67f82d`

Type:

```lean
(inputFormat accumulationFormat : HighamBench.P20StaticBinaryFormat) →
  instLENat.le inputFormat.precision accumulationFormat.precision →
    And (Int.instLEInt.le accumulationFormat.minExponent inputFormat.minExponent)
        (Int.instLEInt.le inputFormat.maxExponent accumulationFormat.maxExponent) →
      (inputRound inputDelta inputEta : Real → Real) →
        (inputNoOverflow : Real → Prop) →
          (∀ {x : Real},
              inputNoOverflow x →
                Eq (inputRound x) (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (inputDelta x))) (inputEta x))) →
            (∀ {x : Real},
                inputNoOverflow x →
                  Real.instLE.le (abs (inputDelta x)) (HighamBench.p20UnitRoundoff inputFormat.precision)) →
              (∀ {x : Real},
                  inputNoOverflow x →
                    Real.instLE.le (abs (inputEta x))
                      (HighamBench.p20UnderflowEnvelope inputFormat.precision inputFormat.minExponent
                        inputFormat.hasSubnormals)) →
                (∀ {x : Real}, inputNoOverflow x → Eq (instHMul.hMul (inputEta x) (inputDelta x)) 0) →
                  (∀ {x : Real}, inputNoOverflow x → HighamBench.p20StaticRepresentable inputFormat (inputRound x)) →
                    (∀ {x : Real},
                        inputNoOverflow x →
                          ∀ {y : Real},
                            HighamBench.p20StaticRepresentable inputFormat y →
                              Real.instLE.le (abs (instHSub.hSub (inputRound x) x)) (abs (instHSub.hSub y x))) →
                      (accumulationRound accumulationDelta accumulationEta : Real → Real) →
                        (accumulationNoOverflow : Real → Prop) →
                          (∀ {x : Real},
                              accumulationNoOverflow x →
                                Eq (accumulationRound x)
                                  (instHAdd.hAdd (instHMul.hMul x (instHAdd.hAdd 1 (accumulationDelta x)))
                                    (accumulationEta x))) →
                            (∀ {x : Real},
                                accumulationNoOverflow x →
                                  Real.instLE.le (abs (accumulationDelta x))
                                    (HighamBench.p20UnitRoundoff accumulationFormat.precision)) →
                              (∀ {x : Real},
                                  accumulationNoOverflow x →
                                    Real.instLE.le (abs (accumulationEta x))
                                      (HighamBench.p20UnderflowEnvelope accumulationFormat.precision
                                        accumulationFormat.minExponent accumulationFormat.hasSubnormals)) →
                                (∀ {x : Real},
                                    accumulationNoOverflow x →
                                      Eq (instHMul.hMul (accumulationEta x) (accumulationDelta x)) 0) →
                                  (∀ {x : Real},
                                      accumulationNoOverflow x →
                                        HighamBench.p20StaticRepresentable accumulationFormat (accumulationRound x)) →
                                    (∀ {x : Real},
                                        accumulationNoOverflow x →
                                          ∀ {y : Real},
                                            HighamBench.p20StaticRepresentable accumulationFormat y →
                                              Real.instLE.le (abs (instHSub.hSub (accumulationRound x) x))
                                                (abs (instHSub.hSub y x))) →
                                      HighamBench.P20StaticNearestModel1
```

Fully explicit type:

```lean
(inputFormat accumulationFormat : HighamBench.P20StaticBinaryFormat) →
  (accumulation_precision :
      @LE.le.{0} Nat instLENat (HighamBench.P20StaticBinaryFormat.precision inputFormat)
        (HighamBench.P20StaticBinaryFormat.precision accumulationFormat)) →
    (accumulation_range :
        And
          (@LE.le.{0} Int Int.instLEInt (HighamBench.P20StaticBinaryFormat.minExponent accumulationFormat)
            (HighamBench.P20StaticBinaryFormat.minExponent inputFormat))
          (@LE.le.{0} Int Int.instLEInt (HighamBench.P20StaticBinaryFormat.maxExponent inputFormat)
            (HighamBench.P20StaticBinaryFormat.maxExponent accumulationFormat))) →
      (inputRound inputDelta inputEta : Real → Real) →
        (inputNoOverflow : Real → Prop) →
          (input_rounding_equation :
              ∀ {x : Real},
                inputNoOverflow x →
                  @Eq.{1} Real (inputRound x)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (inputDelta x)))
                      (inputEta x))) →
            (input_delta_bound :
                ∀ {x : Real},
                  inputNoOverflow x →
                    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (inputDelta x))
                      (HighamBench.p20UnitRoundoff (HighamBench.P20StaticBinaryFormat.precision inputFormat))) →
              (input_eta_bound :
                  ∀ {x : Real},
                    inputNoOverflow x →
                      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (inputEta x))
                        (HighamBench.p20UnderflowEnvelope (HighamBench.P20StaticBinaryFormat.precision inputFormat)
                          (HighamBench.P20StaticBinaryFormat.minExponent inputFormat)
                          (HighamBench.P20StaticBinaryFormat.hasSubnormals inputFormat))) →
                (input_error_exclusive :
                    ∀ {x : Real},
                      inputNoOverflow x →
                        @Eq.{1} Real
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (inputEta x)
                            (inputDelta x))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                  (input_round_representable :
                      ∀ {x : Real}, inputNoOverflow x → HighamBench.p20StaticRepresentable inputFormat (inputRound x)) →
                    (input_round_nearest :
                        ∀ {x : Real},
                          inputNoOverflow x →
                            ∀ {y : Real},
                              HighamBench.p20StaticRepresentable inputFormat y →
                                @LE.le.{0} Real Real.instLE
                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                      (inputRound x) x))
                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) y x))) →
                      (accumulationRound accumulationDelta accumulationEta : Real → Real) →
                        (accumulationNoOverflow : Real → Prop) →
                          (accumulation_rounding_equation :
                              ∀ {x : Real},
                                accumulationNoOverflow x →
                                  @Eq.{1} Real (accumulationRound x)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                          (accumulationDelta x)))
                                      (accumulationEta x))) →
                            (accumulation_delta_bound :
                                ∀ {x : Real},
                                  accumulationNoOverflow x →
                                    @LE.le.{0} Real Real.instLE
                                      (@abs.{0} Real Real.lattice Real.instAddGroup (accumulationDelta x))
                                      (HighamBench.p20UnitRoundoff
                                        (HighamBench.P20StaticBinaryFormat.precision accumulationFormat))) →
                              (accumulation_eta_bound :
                                  ∀ {x : Real},
                                    accumulationNoOverflow x →
                                      @LE.le.{0} Real Real.instLE
                                        (@abs.{0} Real Real.lattice Real.instAddGroup (accumulationEta x))
                                        (HighamBench.p20UnderflowEnvelope
                                          (HighamBench.P20StaticBinaryFormat.precision accumulationFormat)
                                          (HighamBench.P20StaticBinaryFormat.minExponent accumulationFormat)
                                          (HighamBench.P20StaticBinaryFormat.hasSubnormals accumulationFormat))) →
                                (accumulation_error_exclusive :
                                    ∀ {x : Real},
                                      accumulationNoOverflow x →
                                        @Eq.{1} Real
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (accumulationEta x) (accumulationDelta x))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                  (accumulation_round_representable :
                                      ∀ {x : Real},
                                        accumulationNoOverflow x →
                                          HighamBench.p20StaticRepresentable accumulationFormat (accumulationRound x)) →
                                    (accumulation_round_nearest :
                                        ∀ {x : Real},
                                          accumulationNoOverflow x →
                                            ∀ {y : Real},
                                              HighamBench.p20StaticRepresentable accumulationFormat y →
                                                @LE.le.{0} Real Real.instLE
                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                    (@HSub.hSub.{0, 0, 0} Real Real Real
                                                      (@instHSub.{0} Real Real.instSub) (accumulationRound x) x))
                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                    (@HSub.hSub.{0, 0, 0} Real Real Real
                                                      (@instHSub.{0} Real Real.instSub) y x))) →
                                      HighamBench.P20StaticNearestModel1
```

### D049: `HighamBench.p20InfNormVec`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D050: `HighamBench.p20MaximalPowerTwoScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D051: `HighamBench.p20MinNormal`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D052: `HighamBench.p20RetainedWordPairs`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D053: `HighamBench.p20RoundedFoldNoOverflowFrom`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ef4652e0c2e1640d530cf6710ae7278192d50051447ff1d9be584eb64523f8c6`

Type:

```lean
(Real → Prop) → (Real → Real) → Real → List Real → Prop
```

Fully explicit type:

```lean
(allowed : Real → Prop) → (round : Real → Real) → Real → List.{0} Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun allowed round x x_1 =>
  List.brecOn (motive := fun x => Real → Prop) x_1
    (fun x f x_2 =>
      HighamBench.p20RoundedFoldFrom.match_1 (fun x x_3 => List.below (motive := fun x => Real → Prop) x_3 → Prop) x_2 x
        (fun x x_3 => True)
        (fun acc term terms x => And (allowed (instHAdd.hAdd acc term)) (x.1 (round (instHAdd.hAdd acc term)))) f)
    x
```

### D054: `HighamBench.p20ScaleColumns`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D055: `HighamBench.p20ScaleRows`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D056: `HighamBench.p20StaticAWordApproximation`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0e0f486722ff384ea34107ffa26498e71af4645286429f5f234df17729d8b5a7`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run row col =>
  instHMul.hMul (Real.instInv.inv (run.rowScale row))
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) i.val) (run.Aword i row col))
```

### D057: `HighamBench.p20StaticAccumulatedInnerProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7694ab016120f5516b7fce6f06868c55c1af80a1aa4bf4253858ce04d6223930`

Type:

```lean
{n : Nat} → HighamBench.P20StaticNearestModel1 → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (model : HighamBench.P20StaticNearestModel1) → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} model x y =>
  HighamBench.p20RoundedFoldFrom model.accumulationRound 0
    (List.ofFn fun k => model.accumulationRound (instHMul.hMul (x k) (y k)))
```

### D058: `HighamBench.p20StaticAccumulationError`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1577b835eba37e370548479c898404775a0902ad0069a56f41aa9f3565d7bb2c`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run => instHSub.hSub run.computed (HighamBench.p20StaticExactRetainedWordProduct run)
```

### D059: `HighamBench.p20StaticBWordApproximation`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2f8c2d65ade2544bc24af7ce29a4a2b5816ae2e9d8239fc50d0fc311eb8978b4`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run row col =>
  instHMul.hMul
    (Finset.univ.sum fun i =>
      instHMul.hMul (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) i.val) (run.Bword i row col))
    (Real.instInv.inv (run.columnScale col))
```

### D060: `HighamBench.p20StaticExactRetainedWordProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `22f40f502167ac4b00ae6f40b7b33ed05dde5f4c44e0911d67dab0206a2f10c8`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  HighamBench.p20UnscaleProduct run.rowScale run.columnScale fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLTNat.lt (instHAdd.hAdd i.val j.val) p) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword i) (run.Bword j) row col)
```

### D061: `HighamBench.p20StaticInnerProductNoOverflow`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `826f363b00afc08e02a6843a96669eb3ec223a021fc6c250ed72b37cfb9f4988`

Type:

```lean
{n : Nat} → HighamBench.P20StaticNearestModel1 → (Fin n → Real) → (Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (model : HighamBench.P20StaticNearestModel1) → (x y : Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} model x y =>
  And (∀ (k : Fin n), model.accumulationNoOverflow (instHMul.hMul (x k) (y k)))
    (HighamBench.p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow model.accumulationRound 0
      (List.ofFn fun k => model.accumulationRound (instHMul.hMul (x k) (y k))))
```

### D062: `HighamBench.p20StaticOmittedCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f40c81263b16e163be93b5a74357ea09663500c87ccab8155f44bd89ac105369`

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
fun p u => instHMul.hMul (instHSub.hSub p.cast 1) (instHPow.hPow u p)
```

### D063: `HighamBench.p20StaticOmittedWordTail`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e63b52b6e9b34a52d7dcde8d4121a419422c18542572b9880eb02ece7269de59`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  HighamBench.p20UnscaleProduct run.rowScale run.columnScale fun row col =>
    Finset.univ.sum fun i =>
      (Finset.filter (fun j => instLENat.le p (instHAdd.hAdd i.val j.val)) Finset.univ).sum fun j =>
        instHMul.hMul (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) (instHAdd.hAdd i.val j.val))
          (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (run.Aword i) (run.Bword j) row col)
```

### D064: `HighamBench.p20StaticRawAccumulationCoefficient`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eaff75a0cc696245109bca9bace81ab709304742ac9d8f6c1c95a60c2454824d`

Type:

```lean
Nat → Nat → Nat → Real → Real → Real → Real
```

Fully explicit type:

```lean
(n p r : Nat) → (U theta Gmin : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n p r U theta Gmin =>
  instHAdd.hAdd (HighamBench.p20MultiAccumRoundingCoefficient n p U)
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 r.cast) n.cast) (instHPow.hPow (Real.instInv.inv theta) 2)) Gmin)
```

### D065: `HighamBench.p20StaticRetainedWordProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `ee70783f1d6e5a142a213041aa5270117b093930097e0a161da488219ad6b0de`

Type:

```lean
{m n q p : Nat} →
  HighamBench.P20StaticNearestModel1 →
    Real → (Fin p → HighamBench.P20Matrix m n) → (Fin p → HighamBench.P20Matrix n q) → HighamBench.P20Matrix m q
```

Fully explicit type:

```lean
{m n q p : Nat} →
  (model : HighamBench.P20StaticNearestModel1) →
    (u : Real) →
      (Aword : Fin p → HighamBench.P20Matrix m n) →
        (Bword : Fin p → HighamBench.P20Matrix n q) → HighamBench.P20Matrix m q
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} model u Aword Bword row col =>
  HighamBench.p20RoundedFoldFrom model.accumulationRound 0
    (List.map
      (fun pair =>
        instHMul.hMul (instHPow.hPow u (instHAdd.hAdd pair.fst.val pair.snd.val))
          (HighamBench.p20StaticAccumulatedInnerProduct model (Aword pair.fst row) fun k => Bword pair.snd k col))
      (HighamBench.p20RetainedWordPairs p))
```

### D066: `HighamBench.p20StaticZeta`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `de625bb90558acf72843b146c44cb09d35d2e55aabac33910a5f6883282d633b`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → (run : HighamBench.P20StaticMultiwordRun m n q p) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q p} run =>
  Real.instMax.max (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) p)
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 2 n.cast)
          (instHPow.hPow (HighamBench.p20StaticInputUnitRoundoff run.model) (instHSub.hSub p 1)))
        (Real.instInv.inv (HighamBench.p20StaticScalingThreshold n run.model)))
      (HighamBench.p20StaticInputUnderflowEnvelope run.model))
```

### D067: `HighamBench.p20UnderflowEnvelope.match_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D068: `HighamBench.p20UnscaleProduct`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D069: `HighamBench.P20StaticBinaryFormat.mk`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `327623ce0696f27f1520d6987cb953a91fd0d381eab547d1bd9d47de7b854468`

Type:

```lean
(precision : Nat) →
  (minExponent maxExponent : Int) →
    Bool → instLTNat.lt 0 precision → Int.instLEInt.le minExponent maxExponent → HighamBench.P20StaticBinaryFormat
```

Fully explicit type:

```lean
(precision : Nat) →
  (minExponent maxExponent : Int) →
    (hasSubnormals : Bool) →
      (precision_pos :
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) precision) →
        (exponent_range_nonempty : @LE.le.{0} Int Int.instLEInt minExponent maxExponent) →
          HighamBench.P20StaticBinaryFormat
```

### D070: `HighamBench.P20StaticMultiwordRun.Aword`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `704b5129a62de10dcd80ae4e388e2249991e1ae57e4948ec33d70fa76e89e3ca`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Fin p → HighamBench.P20Matrix m n
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → Fin p → HighamBench.P20Matrix m n
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.12
```

### D071: `HighamBench.P20StaticMultiwordRun.Bword`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `50da6318ea901b4de20c795c1f3ba1b168b5199e129c492e05e8df03a5c0c8d1`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Fin p → HighamBench.P20Matrix n q
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → Fin p → HighamBench.P20Matrix n q
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.13
```

### D072: `HighamBench.P20StaticMultiwordRun.columnScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `fb35b2c6920810782d711a24f2636b1017ea41f3b1bc5ff1f438608646c842eb`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Fin q → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → Fin q → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.7
```

### D073: `HighamBench.P20StaticMultiwordRun.rowScale`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `cc1128f2d7fe9d22934381d2a1173b38d73cad49999866a08a1b3e937d618600`

Type:

```lean
{m n q p : Nat} → HighamBench.P20StaticMultiwordRun m n q p → Fin m → Real
```

Fully explicit type:

```lean
{m n q p : Nat} → (self : HighamBench.P20StaticMultiwordRun m n q p) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n q p self => self.6
```

### D074: `HighamBench.p20IsPowerOfTwo`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D075: `HighamBench.p20RoundedFoldFrom`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b9ac3455dcf1dc9cf70fa61923440b2e2fe716dcf75ba3b524efa0a03bdae462`

Type:

```lean
(Real → Real) → Real → List Real → Real
```

Fully explicit type:

```lean
(round : Real → Real) → Real → List.{0} Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun round x x_1 =>
  List.brecOn (motive := fun x => Real → Real) x_1
    (fun x f x_2 =>
      HighamBench.p20RoundedFoldFrom.match_1 (fun x x_3 => List.below (motive := fun x => Real → Real) x_3 → Real) x_2 x
        (fun acc x => acc) (fun acc term terms x => x.1 (round (instHAdd.hAdd acc term))) f)
    x
```

### D076: `HighamBench.p20RoundedFoldFrom.match_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `88e8fa9f2ed16f52b7ea53a3c38334c38387acfcf116f81b9b628eb5a947ab55`

Type:

```lean
(motive : Real → List Real → Sort u_1) →
  (x : Real) →
    (x_1 : List Real) →
      ((acc : Real) → motive acc List.nil) →
        ((acc term : Real) → (terms : List Real) → motive acc (List.cons term terms)) → motive x x_1
```

Fully explicit type:

```lean
(motive : Real → List.{0} Real → Sort u_1) →
  (x : Real) →
    (x_1 : List.{0} Real) →
      (h_1 : (acc : Real) → motive acc (@List.nil.{0} Real)) →
        (h_2 : (acc term : Real) → (terms : List.{0} Real) → motive acc (@List.cons.{0} Real term terms)) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 => List.casesOn x_1 (h_1 x) fun head tail => h_2 x head tail
```

### D077: `HighamBench.p20StaticRepresentable`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `15f338e77ee36f1975190ab90fa08bcc2dec8f8985f1febc2baa471abcca6d8b`

Type:

```lean
HighamBench.P20StaticBinaryFormat → Real → Prop
```

Fully explicit type:

```lean
(format : HighamBench.P20StaticBinaryFormat) → (x : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun format x =>
  Or (Eq x 0)
    (Exists fun sign =>
      And (Or (Eq sign 1) (Eq sign (-1)))
        (Exists fun significand =>
          Exists fun exponent =>
            And
              (Eq x
                (instHMul.hMul (instHMul.hMul sign significand.cast)
                  (instHPow.hPow 2 (instHSub.hSub exponent (instHSub.hSub format.precision 1).cast))))
              (Or
                (And (instLENat.le (instHPow.hPow 2 (instHSub.hSub format.precision 1)) significand)
                  (And (instLTNat.lt significand (instHPow.hPow 2 format.precision))
                    (And (Int.instLEInt.le format.minExponent exponent)
                      (Int.instLEInt.le exponent format.maxExponent))))
                (And (Eq format.hasSubnormals Bool.true)
                  (And (Eq exponent format.minExponent)
                    (And (instLTNat.lt 0 significand)
                      (instLTNat.lt significand (instHPow.hPow 2 (instHSub.hSub format.precision 1)))))))))
```

### D078: `And`

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

### D079: `DivInvMonoid.toDiv`

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

### D080: `Eq`

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

### D081: `HAdd.hAdd`

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

### D082: `HDiv.hDiv`

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

### D083: `HMul.hMul`

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

### D084: `HPow.hPow`

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

### D085: `HSub.hSub`

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

### D086: `Monoid.toNatPow`

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

### D087: `Nat`

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

### D088: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D089: `Nat.instAtLeastTwoHAddOfNat`

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

### D090: `Nat.instNeZeroSucc`

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

### D091: `OfNat.ofNat`

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

### D092: `One.toOfNat1`

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

### D095: `Real.instDivInvMonoid`

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

### D096: `Real.instMonoid`

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

### D097: `Real.instMul`

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

### D098: `Real.instNatCast`

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

### D099: `Real.instOne`

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

### D100: `instHAdd`

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

### D101: `instHDiv`

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

### D102: `instHMul`

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

### D103: `instHPow`

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

### D104: `instHSub`

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

### D105: `instOfNatAtLeastTwo`

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

### D106: `instOfNatNat`

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

### D107: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D108: `Exists`

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

### D109: `Fin`

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

### D110: `Fin.fintype`

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

### D111: `Inv.inv`

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

### D112: `LE.le`

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

### D113: `Matrix`

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

### D114: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

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

### D115: `Matrix.sub`

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

### D116: `Real.instAddCommMonoid`

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

### D117: `Real.instAddGroup`

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

### D118: `Real.instInv`

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

### D119: `Real.instLE`

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

### D123: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D124: `ConditionallyCompleteLinearOrderBot.toOrderBot`

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

### D125: `DivInvMonoid.toZPow`

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

### D126: `Fin.val`

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

### D127: `Finset.filter`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Filter`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D128: `Finset.sum`

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

### D129: `Finset.sup`

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

### D130: `Finset.univ`

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

### D131: `Int`

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

### D132: `LT.lt`

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

### D133: `List.map`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `509306b13208ac7c4830c43f93dc873d045ae0ae6b1984beea3ee3ecf89cb205`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → (f : α → β) → (l : List.{u_1} α) → List.{u_2} β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f x =>
  List.brecOn x fun x f_1 =>
    instDecidableEqList.match_1 (fun x => List.below x → List β) x (fun _ x => List.nil)
      (fun a as x => List.cons (f a) x.1) f_1
```

### D134: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D135: `Min.min`

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

### D136: `NNNorm.nnnorm`

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

### D137: `NNReal`

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

### D138: `NNReal.instConditionallyCompleteLinearOrderBot`

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

### D139: `NNReal.toReal`

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

### D140: `Nat.AtLeastTwo`

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

### D141: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D147: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D148: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D149: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D150: `Real.instMin`

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

### D151: `Real.instZero`

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

### D152: `Real.normedCommRing`

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

### D153: `Real.sqrt`

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

### D154: `SeminormedAddCommGroup.toSeminormedAddGroup`

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

### D155: `SeminormedAddGroup.toNNNorm`

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

### D156: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

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

### D157: `Semiring.toNonAssocSemiring`

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

### D158: `Unit`

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

### D159: `Zero.toOfNat0`

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

### D160: `instAddNat`

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

### D161: `instLTNat`

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

### D162: `instSemilatticeSupNNReal`

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

### D163: `instSemiringNNReal`

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

### D164: `Bool.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D165: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D166: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D167: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D168: `Int.instLEInt`

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

### D169: `List`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `ec06a72bb009eecaedd9dbf6a3349bbea0bbc480e0a21179f4e21b3e219b952d`

Type:

```lean
Type u → Type u
```

Fully explicit type:

```lean
(α : Type u) → Type u
```

### D170: `List.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ee953aef3cdd9f3df3ef9486761906c6ea0dc0de50785a6d5c06dd73fd337b6a`

Type:

```lean
{α : Type u} → {motive : List α → Sort u_1} → List α → Sort (max (u + 1) u_1)
```

Fully explicit type:

```lean
{α : Type u} → {motive : (t : List.{u} α) → Sort u_1} → (t : List.{u} α) → Sort (max (u + 1) u_1)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t => List.rec PUnit (fun head tail tail_ih => PProd (motive tail) tail_ih) t
```

### D171: `List.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `dc2fe7ac5b6c6e21a42444bdb2a571336ead421bcc514f9ad3cb9d7691262fb6`

Type:

```lean
{α : Type u} → {motive : List α → Sort u_1} → (t : List α) → ((t : List α) → List.below t → motive t) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {motive : (t : List.{u} α) → Sort u_1} →
    (t : List.{u} α) → (F_1 : (t : List.{u} α) → (f : @List.below.{u_1, u} α motive t) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t F_1 => (List.brecOn.go t F_1).1
```

### D172: `List.cons`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `d4f0bc0954b11abbe9f8e60dd8762e7797f488b1975b155440101828c4c1ea14`

Type:

```lean
{α : Type u} → α → List α → List α
```

Fully explicit type:

```lean
{α : Type u} → (head : α) → (tail : List.{u} α) → List.{u} α
```

### D173: `List.filter`

- Role: `external-frontier`
- Owner module: `Init.Data.List.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D174: `List.flatten`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D175: `List.nil`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `6fc023f8c03f1dc78130598a9c55a666564e22fa908127753ee95d45e602196f`

Type:

```lean
{α : Type u} → List α
```

Fully explicit type:

```lean
{α : Type u} → List.{u} α
```

### D176: `List.ofFn`

- Role: `external-frontier`
- Owner module: `Init.Data.List.OfFn`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D177: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D178: `Nat.decLe`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D179: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D180: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (fst : α) → (snd : β) → Prod.{u, v} α β
```

### D181: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D182: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D183: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D184: `True`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `151888ac453f6815e1022e38f8b589caefb03395ffd196a9f58c1de8920fa6e1`

Type:

```lean
Prop
```

Fully explicit type:

```lean
Prop
```

### D185: `Unit.unit`

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

### D186: `instLENat`

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

### D187: `Int.instSub`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `cdec027f4b1a52ca9841248e8efbabc901ed4e9b4220aa4074044d4c9537c68c`

Type:

```lean
Sub Int
```

Fully explicit type:

```lean
Sub.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ sub := Int.sub }
```

### D188: `List.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `6d65021c92e6afd6b33fb172f3e220af64038e7d537976362e8538c7a690ea48`

Type:

```lean
{α : Type u} →
  {motive : List α → Sort u_1} →
    (t : List α) → motive List.nil → ((head : α) → (tail : List α) → motive (List.cons head tail)) → motive t
```

Fully explicit type:

```lean
{α : Type u} →
  {motive : (t : List.{u} α) → Sort u_1} →
    (t : List.{u} α) →
      (nil : motive (@List.nil.{u} α)) →
        (cons : (head : α) → (tail : List.{u} α) → motive (@List.cons.{u} α head tail)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {motive} t nil cons => List.rec nil (fun head tail tail_ih => cons head tail) t
```

### D189: `Nat.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `de0cbde8dd75c1a0c6d5d08b9cfa1cd5908aeb874409a1c880c9c9616deb1709`

Type:

```lean
Monoid Nat
```

Fully explicit type:

```lean
Monoid.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D190: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D191: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D192: `instNatCastInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7fb46bceee4f1142c75008c8ac4be64c11c4bdbc7972ff89c0a5335ad80a2033`

Type:

```lean
NatCast Int
```

Fully explicit type:

```lean
NatCast.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => Int.ofNat n }
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

### `HighamBench.P20Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P20Definitions.lean`
SHA-256: `3fda14f944d37cc4740956ac7c63f8341aa3cfcf2d8308f888f40908e410b490`

```lean
import HighamBench.Core
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

/-- The explicit finite maximum of the absolute vector coefficients used as
the infinity norm around equations (3.1)--(3.4). -/
noncomputable def p20InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => Real.toNNReal |x i|) : NNReal) : ℝ)

/-- Scale a finite row or column by a real power-of-two factor. -/
def p20ScaleVec {n : ℕ} (lambda : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda * x i

/-- The largest safe scaled-input magnitude from equation (3.2). -/
noncomputable def p20ScalingThreshold (n : ℕ) (fmax Fmax : ℝ) : ℝ :=
  min fmax (Real.sqrt (Fmax / (n : ℝ)))

/-- Exact powers of two used for the diagonal scaling factors in (3.1). -/
def p20IsPowerOfTwo (lambda : ℝ) : Prop :=
  ∃ exponent : ℤ, lambda = (2 : ℝ) ^ exponent

/-- Select the exponent whose power of two lies immediately below
`theta / ‖x‖∞`. The fallback is irrelevant for the positive ratios required
by equation (3.4a). -/
noncomputable def p20RowScaleExponent {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℤ :=
  if hratio : 0 < theta / p20InfNormVec x then
    Classical.choose
      (exists_mem_Ico_zpow hratio (by norm_num : (1 : ℝ) < 2))
  else
    0

/-- The row-specific power-of-two factor `lambda_i` selected for (3.4a). -/
noncomputable def p20RowScaleFactor {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℝ :=
  (2 : ℝ) ^ p20RowScaleExponent theta x

/-- The diagonal matrix `Lambda` from equation (3.1). -/
noncomputable def p20RowScalingMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => p20RowScaleFactor theta (A i))

/-- The exactly scaled input `Lambda A` from equation (3.1). -/
noncomputable def p20LeftScaledMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  p20RowScalingMatrix theta A * A

/-- Paper-scoped rectangular infinity norm (maximum absolute row sum). -/
noncomputable def p20InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

/-- The input-underflow part of the simplified single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowBound {m n q : ℕ}
    (theta gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The accumulation-underflow part of the simplified single-word bound
(3.26). -/
noncomputable def p20SingleAccumUnderflowBound {m n q : ℕ}
    (theta Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * (theta⁻¹) ^ 2 * Gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The input-rounding term in the multiword bound (4.32). -/
def p20MultiInputRoundingCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p

/-- The input-rounding term in the single-word bound (3.26). -/
def p20SingleInputRoundingCoefficient (u : ℝ) : ℝ :=
  2 * u

/-- The input-underflow coefficient in the single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowCoefficient
    (n : ℕ) (theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin

/-- The accumulation-rounding term in the multiword bound (4.32). -/
def p20MultiAccumRoundingCoefficient (n p : ℕ) (U : ℝ) : ℝ :=
  ((n : ℝ) + (p : ℝ) ^ 2) * U

/-- The range-unrestricted coefficient in the multiword bound (4.33). -/
def p20MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  p20MultiInputRoundingCoefficient p u +
    p20MultiAccumRoundingCoefficient n p U

/-- The input-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

/-- The accumulation-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

/-- The complete narrow-range coefficient in the multiword bound (4.32). -/
noncomputable def p20MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p20MultiRangeFreeCoefficient n p u U +
    p20MultiInputUnderflowCoefficient n p u theta gmin +
      p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- Apply a scalar coefficient to the product of the two rectangular matrix
infinity norms appearing in (3.26), (4.32), and (4.33). -/
noncomputable def p20NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p20InfNormRect A * p20InfNormRect B

/-! ## Multiword execution model for Theorem 4.1 -/

/-- A finite rectangular real matrix in the P20 model. -/
abbrev P20Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The unit roundoff `2^(-t)` of a binary format with `t` precision bits. -/
noncomputable def p20UnitRoundoff (precision : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ precision

/-- The smallest positive normalized value of a binary format. -/
noncomputable def p20MinNormal (minExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ minExponent

/-- The largest finite value of the binary format used in Model 1. -/
noncomputable def p20MaxFinite (precision : ℕ) (maxExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ maxExponent * (2 - 2 * p20UnitRoundoff precision)

/-- The `g_min` or `G_min` envelope from (2.1)--(2.2). -/
noncomputable def p20UnderflowEnvelope (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) : ℝ :=
  match hasSubnormals with
  | false => p20MinNormal minExponent / 2
  | true => p20UnitRoundoff precision * p20MinNormal minExponent

/-- A precision-parametrized binary floating-point format from Model 1. -/
structure P20BinaryFormatFamily (ι : Type*) where
  precision : ι → ℕ
  minExponent : ι → ℤ
  maxExponent : ι → ℤ
  hasSubnormals : ι → Bool
  precision_pos : ∀ t, 0 < precision t
  exponent_range_nonempty : ∀ t, minExponent t ≤ maxExponent t

/-- Unit roundoff of one member of a format family. -/
noncomputable def p20FormatUnitRoundoff {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnitRoundoff (format.precision t)

/-- Largest finite value of one member of a format family. -/
noncomputable def p20FormatMaxFinite {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20MaxFinite (format.precision t) (format.maxExponent t)

/-- Underflow envelope of one member of a format family. -/
noncomputable def p20FormatUnderflowEnvelope {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnderflowEnvelope (format.precision t) (format.minExponent t)
    (format.hasSubnormals t)

/-- Model 1: input and accumulation formats, their nesting, and the two
rounding models (2.3)--(2.4). The maps represent operations for which overflow
does not occur. -/
structure P20Model1 (ι : Type*) where
  inputFormat : P20BinaryFormatFamily ι
  accumulationFormat : P20BinaryFormatFamily ι
  accumulation_precision : ∀ t,
    inputFormat.precision t ≤ accumulationFormat.precision t
  accumulation_range : ∀ t,
    accumulationFormat.minExponent t ≤ inputFormat.minExponent t ∧
      inputFormat.maxExponent t ≤ accumulationFormat.maxExponent t
  inputRound : ι → ℝ → ℝ
  inputDelta : ι → ℝ → ℝ
  inputEta : ι → ℝ → ℝ
  input_rounding_equation : ∀ t x,
    inputRound t x = x * (1 + inputDelta t x) + inputEta t x
  input_delta_bound : ∀ t x,
    |inputDelta t x| ≤ p20FormatUnitRoundoff inputFormat t
  input_eta_bound : ∀ t x,
    |inputEta t x| ≤ p20FormatUnderflowEnvelope inputFormat t
  input_error_exclusive : ∀ t x, inputEta t x * inputDelta t x = 0
  accumulationRound : ι → ℝ → ℝ
  accumulationDelta : ι → ℝ → ℝ
  accumulationEta : ι → ℝ → ℝ
  accumulation_rounding_equation : ∀ t x,
    accumulationRound t x =
      x * (1 + accumulationDelta t x) + accumulationEta t x
  accumulation_delta_bound : ∀ t x,
    |accumulationDelta t x| ≤
      p20FormatUnitRoundoff accumulationFormat t
  accumulation_eta_bound : ∀ t x,
    |accumulationEta t x| ≤
      p20FormatUnderflowEnvelope accumulationFormat t
  accumulation_error_exclusive : ∀ t x,
    accumulationEta t x * accumulationDelta t x = 0

/-- The input-format unit roundoff `u` of Model 1. -/
noncomputable def p20InputUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.inputFormat t

/-- The accumulation-format unit roundoff `U` of Model 1. -/
noncomputable def p20AccumUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.accumulationFormat t

/-- The input-format underflow envelope `g_min` of Model 1. -/
noncomputable def p20InputUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.inputFormat t

/-- The accumulation-format underflow envelope `G_min` of Model 1. -/
noncomputable def p20AccumUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.accumulationFormat t

/-- The format-derived scaling threshold `theta` from (3.2). -/
noncomputable def p20ModelScalingThreshold {ι : Type*}
    (n : ℕ) (model : P20Model1 ι) (t : ι) : ℝ :=
  p20ScalingThreshold n
    (p20FormatMaxFinite model.inputFormat t)
    (p20FormatMaxFinite model.accumulationFormat t)

/-- Exact row scaling by the diagonal entries of `Lambda`. -/
def p20ScaleRows {m n : ℕ} (lambda : Fin m → ℝ)
    (A : P20Matrix m n) : P20Matrix m n :=
  fun i j => lambda i * A i j

/-- Exact column scaling by the diagonal entries of `M`. -/
def p20ScaleColumns {n q : ℕ} (B : P20Matrix n q)
    (mu : Fin q → ℝ) : P20Matrix n q :=
  fun i j => B i j * mu j

/-- The maximal-power-of-two scaling rule inherited from (3.4a)--(3.4b).
The zero-vector branch records an explicit harmless convention omitted by the
paper. -/
def p20MaximalPowerTwoScale (theta vectorNorm lambda : ℝ) : Prop :=
  p20IsPowerOfTwo lambda ∧ 0 < lambda ∧
    ((vectorNorm = 0 ∧ lambda = 1) ∨
      (0 < vectorNorm ∧ theta / (2 * vectorNorm) < lambda ∧
        lambda ≤ theta / vectorNorm))

/-! ## Single-word scaled-input error from equations (3.3)--(3.13) -/

/-- The exact absolute inner product `|x|^T |y|` in (3.9)--(3.14). -/
noncomputable def p20AbsInnerProduct {n : ℕ}
    (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| * |y i|

/-- The scaled and componentwise input-rounded inner product `s` from (3.3),
before any accumulation-format rounding is applied. -/
noncomputable def p20ScaledInputInnerProduct {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (lambda mu : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  lambda⁻¹ * mu⁻¹ *
    ∑ i : Fin n,
      model.inputRound t (lambda * x i) *
        model.inputRound t (mu * y i)

/-- The input-rounding and input-underflow error `epsilon_1` from (3.8). -/
noncomputable def p20InputStageError {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (lambda mu : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  p20ScaledInputInnerProduct model t lambda mu x y -
    ∑ i : Fin n, x i * y i

/-- The exact right-hand side of equation (3.13). -/
noncomputable def p20InputStageErrorEnvelope {n : ℕ}
    (u gmin theta : ℝ) (x y : Fin n → ℝ) : ℝ :=
  (2 * u + u ^ 2) * p20AbsInnerProduct x y +
    4 * (n : ℝ) * theta⁻¹ * gmin *
      (1 + u + theta⁻¹ * gmin) *
        p20InfNormVec x * p20InfNormVec y

/-- An accumulation-format inner product. Each multiply-add result is rounded
by the accumulation map from Model 1. -/
noncomputable def p20AccumulatedInnerProduct {n : ℕ}
    (round : ℝ → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (List.ofFn fun k : Fin n => x k * y k).foldl
    (fun sum product => round (sum + product)) 0

/-- The retained word-index pairs from (4.31), in lexicographic execution
order. -/
def p20RetainedWordPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.ofFn fun i : Fin p =>
    (List.ofFn fun j : Fin p => (i, j)).filter
      (fun pair => decide (pair.1.val + pair.2.val < p))).flatten

/-- The accumulated expression inside the inverse scalings in (4.31): retain
precisely the word pairs with `i+j<p`, weight them by `u^(i+j)`, and round
their running sum in the accumulation format. -/
noncomputable def p20RetainedWordProduct {m n q p : ℕ}
    (round : ℝ → ℝ) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    (p20RetainedWordPairs p).foldl
      (fun sum pair =>
        round
          (sum + u ^ (pair.1.val + pair.2.val) *
            p20AccumulatedInnerProduct round (Aword pair.1 row)
              (fun k => Bword pair.2 k col))) 0

/-- Undo the diagonal row and column scalings around the retained word
product, as in (4.31). -/
noncomputable def p20UnscaleProduct {m q : ℕ} (lambda : Fin m → ℝ)
    (mu : Fin q → ℝ) (C : P20Matrix m q) : P20Matrix m q :=
  fun i j => (lambda i)⁻¹ * C i j * (mu j)⁻¹

/-- One computed instance of the scaled p-word algorithm (4.29)--(4.31).
The scaling clauses include the lower endpoints used in the derivation of
Theorem 4.1, not only the upper bounds printed in its statement. -/
structure P20MultiwordRun (m n q p : ℕ) (ι : Type*) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20Model1 ι
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : ι → Fin m → ℝ
  columnScale : ι → Fin q → ℝ
  row_scaling_rule : ∀ t i,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (A i)) (rowScale t i)
  column_scaling_rule : ∀ t j,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (fun i => B i j)) (columnScale t j)
  scaled_A_bound : ∀ t i j,
    |p20ScaleRows (rowScale t) A i j| ≤
      p20ModelScalingThreshold n model t
  scaled_B_bound : ∀ t i j,
    |p20ScaleColumns B (columnScale t) i j| ≤
      p20ModelScalingThreshold n model t
  Aword : ι → Fin p → P20Matrix m n
  Bword : ι → Fin p → P20Matrix n q
  Aword_equation : ∀ t i row col,
    Aword t i row col = model.inputRound t
      ((p20ScaleRows (rowScale t) A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Aword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  Bword_equation : ∀ t i row col,
    Bword t i row col = model.inputRound t
      ((p20ScaleColumns B (columnScale t) row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Bword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  computed : ι → P20Matrix m q
  computed_equation : ∀ t,
    computed t = p20UnscaleProduct (rowScale t) (columnScale t)
      (p20RetainedWordProduct (model.accumulationRound t)
        (p20InputUnitRoundoff model t) (Aword t) (Bword t))

/-- Reconstruct `A` from all `p` input words and undo `Lambda`, as in (4.18). -/
noncomputable def p20AWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m n :=
  fun row col =>
    (run.rowScale t row)⁻¹ *
      ∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Aword t i row col

/-- Reconstruct `B` from all `p` input words and undo `M`, as in (4.19). -/
noncomputable def p20BWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Bword t i row col) *
      (run.columnScale t col)⁻¹

/-- The retained part of (4.31) with exact inner products and exact summation.
Its difference from the computed value isolates accumulation-format errors. -/
noncomputable def p20ExactRetainedWordProduct {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The products omitted from (4.31), namely all word pairs with `i+j>=p`. -/
noncomputable def p20OmittedWordTail {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The actual normwise forward error of one execution of (4.31). -/
noncomputable def p20MultiwordForwardError {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : ℝ :=
  p20InfNormRect (run.computed t - run.A * run.B)

/-- The combined first-order scale whose square classifies the terms hidden
by `lesssim` in (4.26)--(4.32). Dimensions and `p` are fixed along the filter. -/
noncomputable def p20MultiwordPrecisionScale {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) : ι → ℝ :=
  fun t =>
    p20InputUnitRoundoff run.model t ^ p +
      p20InputUnitRoundoff run.model t ^ (p - 1) *
        (p20ModelScalingThreshold n run.model t)⁻¹ *
          p20InputUnderflowEnvelope run.model t +
      p20AccumUnitRoundoff run.model t +
      (p20ModelScalingThreshold n run.model t)⁻¹ ^ 2 *
        p20AccumUnderflowEnvelope run.model t

/-- A scalar or norm remainder that is second order in the precision scale. -/
def p20SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t => scale t ^ 2

/-- A precise first-order interpretation of the paper's `lesssim`: the
displayed inequality holds modulo an explicitly second-order remainder. -/
def p20FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p20SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The exact decomposition identities from (4.18)--(4.24), split into
relative-rounding and underflow parts. These identities tie every subsequent
contribution to the words and computed matrix in `run`. -/
structure P20MultiwordErrorData {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) where
  AInputRoundingError : ι → P20Matrix m n
  AInputUnderflowError : ι → P20Matrix m n
  BInputRoundingError : ι → P20Matrix n q
  BInputUnderflowError : ι → P20Matrix n q
  accumulationRoundingError : ι → P20Matrix m q
  accumulationUnderflowError : ι → P20Matrix m q
  A_decomposition : ∀ t,
    run.A = p20AWordApproximation run t + AInputRoundingError t +
      AInputUnderflowError t
  B_decomposition : ∀ t,
    run.B = p20BWordApproximation run t + BInputRoundingError t +
      BInputUnderflowError t
  retained_partition : ∀ t,
    p20ExactRetainedWordProduct run t =
      p20AWordApproximation run t * p20BWordApproximation run t -
        p20OmittedWordTail run t
  accumulation_decomposition : ∀ t,
    run.computed t = p20ExactRetainedWordProduct run t +
      accumulationRoundingError t + accumulationUnderflowError t
  A_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    AInputRoundingError t = 0
  B_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    BInputRoundingError t = 0
  A_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    AInputUnderflowError t = 0
  B_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    BInputUnderflowError t = 0
  accumulation_rounding_zero : ∀ t, run.model.accumulationDelta t = 0 →
    accumulationRoundingError t = 0
  accumulation_underflow_zero : ∀ t, run.model.accumulationEta t = 0 →
    accumulationUnderflowError t = 0

/-- The first-order input-rounding contribution: the two linear decomposition
errors and the omitted `i+j>=p` tail. -/
noncomputable def p20InputRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputRoundingError t * run.B) -
    run.A * data.BInputRoundingError t - p20OmittedWordTail run t

/-- The two linear input-underflow contributions. -/
noncomputable def p20InputUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputUnderflowError t * run.B) -
    run.A * data.BInputUnderflowError t

/-- The accumulation-rounding contribution in the exact computed output. -/
def p20AccumRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationRoundingError t

/-- The accumulation-underflow contribution in the exact computed output. -/
def p20AccumUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationUnderflowError t

/-- The exact residual after removing the four displayed first-order
contributions from the actual computed forward-error matrix. -/
noncomputable def p20ForwardRemainder {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) : P20Matrix m q :=
  run.computed t - run.A * run.B - p20InputRoundingContribution data t -
    p20InputUnderflowContribution data t -
      p20AccumRoundingContribution data t -
        p20AccumUnderflowContribution data t

/-- Exact additive decomposition of the computed forward error. -/
theorem p20ForwardError_decomposition {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) :
    run.computed t - run.A * run.B =
      p20InputRoundingContribution data t +
        p20InputUnderflowContribution data t +
          p20AccumRoundingContribution data t +
            p20AccumUnderflowContribution data t +
              p20ForwardRemainder run data t := by
  unfold p20ForwardRemainder
  abel

/-- The four-source propagation certificate for the derivation
(4.18)--(4.28). It stores source-derived component estimates and a second-order
remainder, but not the final bound (4.32). -/
structure P20MultiwordForwardAnalysis {m n q p : ℕ} {ι : Type*}
    {l : Filter ι} (run : P20MultiwordRun m n q p ι) where
  data : P20MultiwordErrorData run
  input_rounding_bound : ∀ t,
    p20InfNormRect (p20InputRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputRoundingCoefficient p
          (p20InputUnitRoundoff run.model t)) run.A run.B
  input_underflow_bound : ∀ t,
    p20InfNormRect (p20InputUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputUnderflowCoefficient n p
          (p20InputUnitRoundoff run.model t)
          (p20ModelScalingThreshold n run.model t)
          (p20InputUnderflowEnvelope run.model t)) run.A run.B
  accumulation_rounding_bound : ∀ t,
    p20InfNormRect (p20AccumRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumRoundingCoefficient n p
          (p20AccumUnitRoundoff run.model t)) run.A run.B
  accumulation_underflow_bound : ∀ t,
    p20InfNormRect (p20AccumUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumUnderflowCoefficient n p
          (p20ModelScalingThreshold n run.model t)
          (p20AccumUnderflowEnvelope run.model t)) run.A run.B
  remainder_second_order :
    p20SecondOrderAt l (p20MultiwordPrecisionScale run)
      (fun t => p20InfNormRect (p20ForwardRemainder run data t))

/-- Dot-notation projection of the fixed higher-order remainder. -/
noncomputable def P20MultiwordForwardAnalysis.remainder
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20ForwardRemainder run analysis.data

/-- Dot-notation projection of the fixed input-rounding contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputRoundingContribution analysis.data

/-- Dot-notation projection of the fixed input-underflow contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputUnderflowContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-rounding contribution. -/
def P20MultiwordForwardAnalysis.accumulationRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumRoundingContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-underflow contribution. -/
def P20MultiwordForwardAnalysis.accumulationUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumUnderflowContribution analysis.data

/-- Dot-notation form of the exact additive decomposition. -/
theorem P20MultiwordForwardAnalysis.error_decomposition
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) (t : ι) :
    run.computed t - run.A * run.B =
      analysis.inputRoundingContribution t +
        analysis.inputUnderflowContribution t +
          analysis.accumulationRoundingContribution t +
            analysis.accumulationUnderflowContribution t +
              analysis.remainder t := by
  exact p20ForwardError_decomposition run analysis.data t

/-- A proof-carrying execution of every hypothesis and intermediate error
category used to obtain Theorem 4.1. -/
structure P20Theorem41Execution (m n q p : ℕ) (ι : Type*)
    (l : Filter ι) where
  run : P20MultiwordRun m n q p ι
  analysis : P20MultiwordForwardAnalysis (l := l) run

/-! ## Static Theorem 4.1 reconstruction -/

/-- A fixed-instance interpretation of the paper's first-order comparison.
The predicate classifying omitted terms is closed under the operations needed
to combine the independently derived Section 4 remainders. -/
structure P20FirstOrderSemantics where
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0
  add_secondOrder : ∀ {x y}, secondOrder x → secondOrder y →
    secondOrder (x + y)
  abs_secondOrder : ∀ {x}, secondOrder x → secondOrder |x|

/-- The fixed, pointwise meaning of `lhs lesssim rhs`: an exact inequality
after retaining one scalar term classified as second order. -/
def p20FirstOrderLe (semantics : P20FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

/-- The integer parameters of one fixed binary format. -/
structure P20StaticBinaryFormat where
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  hasSubnormals : Bool
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent ≤ maxExponent

/-- The finite real values represented by a fixed binary format. Normal
significands have `precision` bits. When enabled, subnormals use the same
spacing at `minExponent` and a shorter positive significand. -/
def p20StaticRepresentable (format : P20StaticBinaryFormat)
    (x : ℝ) : Prop :=
  x = 0 ∨
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ significand : ℕ, ∃ exponent : ℤ,
        x = sign * (significand : ℝ) *
            (2 : ℝ) ^
              (exponent - (format.precision - 1 : ℕ)) ∧
          ((2 ^ (format.precision - 1) ≤ significand ∧
              significand < 2 ^ format.precision ∧
              format.minExponent ≤ exponent ∧
              exponent ≤ format.maxExponent) ∨
            (format.hasSubnormals = true ∧
              exponent = format.minExponent ∧
              0 < significand ∧
              significand < 2 ^ (format.precision - 1)))

/-- Model 1 at one fixed pair of formats. The inherited error equations are
supplemented with the source's default round-to-nearest meaning. The
`NoOverflow` predicates delimit the operations on which rounding is defined;
the algorithm below certifies that every operation it executes lies there. -/
structure P20StaticNearestModel1 where
  inputFormat : P20StaticBinaryFormat
  accumulationFormat : P20StaticBinaryFormat
  accumulation_precision :
    inputFormat.precision ≤ accumulationFormat.precision
  accumulation_range :
    accumulationFormat.minExponent ≤ inputFormat.minExponent ∧
      inputFormat.maxExponent ≤ accumulationFormat.maxExponent
  inputRound : ℝ → ℝ
  inputDelta : ℝ → ℝ
  inputEta : ℝ → ℝ
  inputNoOverflow : ℝ → Prop
  input_rounding_equation : ∀ {x}, inputNoOverflow x →
    inputRound x = x * (1 + inputDelta x) + inputEta x
  input_delta_bound : ∀ {x}, inputNoOverflow x →
    |inputDelta x| ≤ p20UnitRoundoff inputFormat.precision
  input_eta_bound : ∀ {x}, inputNoOverflow x →
    |inputEta x| ≤
      p20UnderflowEnvelope inputFormat.precision inputFormat.minExponent
        inputFormat.hasSubnormals
  input_error_exclusive : ∀ {x}, inputNoOverflow x →
    inputEta x * inputDelta x = 0
  input_round_representable : ∀ {x}, inputNoOverflow x →
    p20StaticRepresentable inputFormat (inputRound x)
  input_round_nearest : ∀ {x}, inputNoOverflow x →
    ∀ {y}, p20StaticRepresentable inputFormat y →
      |inputRound x - x| ≤ |y - x|
  accumulationRound : ℝ → ℝ
  accumulationDelta : ℝ → ℝ
  accumulationEta : ℝ → ℝ
  accumulationNoOverflow : ℝ → Prop
  accumulation_rounding_equation : ∀ {x}, accumulationNoOverflow x →
    accumulationRound x =
      x * (1 + accumulationDelta x) + accumulationEta x
  accumulation_delta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationDelta x| ≤
      p20UnitRoundoff accumulationFormat.precision
  accumulation_eta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationEta x| ≤
      p20UnderflowEnvelope accumulationFormat.precision
        accumulationFormat.minExponent accumulationFormat.hasSubnormals
  accumulation_error_exclusive : ∀ {x}, accumulationNoOverflow x →
    accumulationEta x * accumulationDelta x = 0
  accumulation_round_representable : ∀ {x}, accumulationNoOverflow x →
    p20StaticRepresentable accumulationFormat (accumulationRound x)
  accumulation_round_nearest : ∀ {x}, accumulationNoOverflow x →
    ∀ {y}, p20StaticRepresentable accumulationFormat y →
      |accumulationRound x - x| ≤ |y - x|

/-- Input-format unit roundoff in the fixed Model-1 contract. -/
noncomputable def p20StaticInputUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.inputFormat.precision

/-- Accumulation-format unit roundoff in the fixed Model-1 contract. -/
noncomputable def p20StaticAccumUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.accumulationFormat.precision

/-- Input-format underflow envelope in the fixed Model-1 contract. -/
noncomputable def p20StaticInputUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.inputFormat.precision
    model.inputFormat.minExponent model.inputFormat.hasSubnormals

/-- Accumulation-format underflow envelope in the fixed Model-1 contract. -/
noncomputable def p20StaticAccumUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.accumulationFormat.precision
    model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals

/-- The fixed threshold `theta = min(fmax, sqrt(Fmax / n))`. -/
noncomputable def p20StaticScalingThreshold (n : ℕ)
    (model : P20StaticNearestModel1) : ℝ :=
  p20ScalingThreshold n
    (p20MaxFinite model.inputFormat.precision
      model.inputFormat.maxExponent)
    (p20MaxFinite model.accumulationFormat.precision
      model.accumulationFormat.maxExponent)

/-- A rounded left fold, used only after every exact product has itself been
rounded to the accumulation format. -/
def p20RoundedFoldFrom (round : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | acc, [] => acc
  | acc, term :: terms =>
      p20RoundedFoldFrom round (round (acc + term)) terms

/-- Every addition argument visited by `p20RoundedFoldFrom` is in the
no-overflow domain. -/
def p20RoundedFoldNoOverflowFrom (allowed : ℝ → Prop)
    (round : ℝ → ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, term :: terms =>
      allowed (acc + term) ∧
        p20RoundedFoldNoOverflowFrom allowed round
          (round (acc + term)) terms

/-- An accumulation-format inner product that rounds each multiplication and
then each addition, as required by equation (2.4). -/
noncomputable def p20StaticAccumulatedInnerProduct {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : ℝ :=
  p20RoundedFoldFrom model.accumulationRound 0
    ((List.ofFn fun k : Fin n =>
      model.accumulationRound (x k * y k)))

/-- No overflow occurs in either the multiplications or the additions of one
executed accumulation-format inner product. -/
def p20StaticInnerProductNoOverflow {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : Prop :=
  (∀ k, model.accumulationNoOverflow (x k * y k)) ∧
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        (List.ofFn fun k : Fin n =>
          model.accumulationRound (x k * y k))

/-- The triangular computation in (4.31). Each retained matrix-product inner
product is executed by `p20StaticAccumulatedInnerProduct`, and the retained
word products are then added in the accumulation format. The powers of `u`
are exact binary scalings. -/
noncomputable def p20StaticRetainedWordProduct {m n q p : ℕ}
    (model : P20StaticNearestModel1) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    p20RoundedFoldFrom model.accumulationRound 0
      ((p20RetainedWordPairs p).map (fun pair =>
        u ^ (pair.1.val + pair.2.val) *
          p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
            (fun k => Bword pair.2 k col)))

/-- One fixed execution of equations (4.29)-(4.31). It contains no propagated
error estimate or final theorem bound. -/
structure P20StaticMultiwordRun (m n q p : ℕ) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20StaticNearestModel1
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : Fin m → ℝ
  columnScale : Fin q → ℝ
  row_scaling_rule : ∀ i,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (A i)) (rowScale i)
  column_scaling_rule : ∀ j,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (fun i => B i j)) (columnScale j)
  scaled_A_bound : ∀ i j,
    |p20ScaleRows rowScale A i j| ≤ p20StaticScalingThreshold n model
  scaled_B_bound : ∀ i j,
    |p20ScaleColumns B columnScale i j| ≤
      p20StaticScalingThreshold n model
  Aword : Fin p → P20Matrix m n
  Bword : Fin p → P20Matrix n q
  Aword_equation : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    Aword i row col = model.inputRound
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Aword_no_overflow : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    model.inputNoOverflow
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_equation : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    Bword i row col = model.inputRound
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_no_overflow : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    model.inputNoOverflow
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  accumulation_no_overflow : ∀ (i j : Fin p),
    i.val + j.val < p → ∀ (row : Fin m) (col : Fin q),
      p20StaticInnerProductNoOverflow model (Aword i row)
        (fun k => Bword j k col)
  retained_sum_no_overflow : ∀ (row : Fin m) (col : Fin q),
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        ((p20RetainedWordPairs p).map (fun pair =>
          p20StaticInputUnitRoundoff model ^
              (pair.1.val + pair.2.val) *
            p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
              (fun k => Bword pair.2 k col)))
  computed : P20Matrix m q
  computed_equation :
    computed = p20UnscaleProduct rowScale columnScale
      (p20StaticRetainedWordProduct model
        (p20StaticInputUnitRoundoff model) Aword Bword)

/-- Reconstruct `A` from all p words and undo the row scaling. -/
noncomputable def p20StaticAWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m n :=
  fun row col =>
    (run.rowScale row)⁻¹ *
      ∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Aword i row col

/-- Reconstruct `B` from all p words and undo the column scaling. -/
noncomputable def p20StaticBWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Bword i row col) *
      (run.columnScale col)⁻¹

/-- The retained p-word product with exact real inner products. -/
noncomputable def p20StaticExactRetainedWordProduct {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

/-- The word products omitted by the triangular condition `i+j<p`. -/
noncomputable def p20StaticOmittedWordTail {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

/-- The accumulation-format error of the actually executed retained product. -/
noncomputable def p20StaticAccumulationError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  run.computed - p20StaticExactRetainedWordProduct run

/-- The fixed normwise forward error in Theorem 4.1. -/
noncomputable def p20StaticMultiwordForwardError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  p20InfNormRect (run.computed - run.A * run.B)

/-- The decomposition coefficient zeta from equation (4.20). -/
noncomputable def p20StaticZeta {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  max (p20StaticInputUnitRoundoff run.model ^ p)
    (2 * (n : ℝ) * p20StaticInputUnitRoundoff run.model ^ (p - 1) *
      (p20StaticScalingThreshold n run.model)⁻¹ *
        p20StaticInputUnderflowEnvelope run.model)

/-- The omitted-product coefficient in equation (4.26). -/
def p20StaticOmittedCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) - 1) * u ^ p

/-- The final accumulation coefficient after applying the source's bound on
the number `r` of possible underflows in one output coefficient. -/
noncomputable def p20StaticAccumulationCoefficient
    (n p : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- The unsimplified coefficient in (4.27), before substituting the bound on
the possible-underflow count `r`. -/
noncomputable def p20StaticRawAccumulationCoefficient
    (n p r : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    4 * (r : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin

/-- The source-local Section 4 estimates used before Theorem 4.1. This stores
the matrix and retained-product decompositions needed to derive (4.21)-(4.25),
the two zeta bounds, and the separate pre-theorem estimates (4.26)-(4.27). It
does not contain (4.28), (4.32), the collected four-term coefficient, or a
final forward-error bound. -/
structure P20StaticSection4Derivation
    (semantics : P20FirstOrderSemantics) {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) where
  AError : P20Matrix m n
  BError : P20Matrix n q
  A_decomposition :
    run.A = p20StaticAWordApproximation run + AError
  B_decomposition :
    run.B = p20StaticBWordApproximation run + BError
  A_error_bound :
    p20InfNormRect AError ≤ p20StaticZeta run * p20InfNormRect run.A
  B_error_bound :
    p20InfNormRect BError ≤ p20StaticZeta run * p20InfNormRect run.B
  retained_partition :
    p20StaticExactRetainedWordProduct run =
      p20StaticAWordApproximation run *
          p20StaticBWordApproximation run -
        p20StaticOmittedWordTail run
  omittedRemainder : ℝ
  omitted_remainder_second_order :
    semantics.secondOrder omittedRemainder
  omitted_tail_bound :
    p20InfNormRect (p20StaticOmittedWordTail run) ≤
      p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        |omittedRemainder|
  accumulationRemainder : ℝ
  accumulation_remainder_second_order :
    semantics.secondOrder accumulationRemainder
  underflowCount : ℕ
  underflow_count_bound :
    (underflowCount : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2
  accumulation_error_bound :
    p20InfNormRect (p20StaticAccumulationError run) ≤
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        |accumulationRemainder|
  quadratic_second_order :
    semantics.secondOrder
      (p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B)

end HighamBench
```
