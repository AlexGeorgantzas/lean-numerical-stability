# Declaration dossier for P13-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p13_t1_condition_ge_one {n : ℕ} (problem : P13LagrangeProblem n)
    (hvalue : p13LagrangeValue problem ≠ 0) :
    p13IsComponentwiseConditionNumber
        (p13LagrangeBasisValues problem) problem.data
        (p13Condition (p13LagrangeBasisValues problem) problem.data) ∧
      1 ≤ p13Condition (p13LagrangeBasisValues problem) problem.data
```

## Elaborated target type

```lean
∀ {n : Nat} (problem : HighamBench.P13LagrangeProblem n),
  Ne (HighamBench.p13LagrangeValue problem) 0 →
    And
      (HighamBench.p13IsComponentwiseConditionNumber (HighamBench.p13LagrangeBasisValues problem) problem.data
        (HighamBench.p13Condition (HighamBench.p13LagrangeBasisValues problem) problem.data))
      (Real.instLE.le 1 (HighamBench.p13Condition (HighamBench.p13LagrangeBasisValues problem) problem.data))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (problem : HighamBench.P13LagrangeProblem n)
  (hvalue :
    @Ne.{1} Real (@HighamBench.p13LagrangeValue n problem)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  And
    (@HighamBench.p13IsComponentwiseConditionNumber
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HighamBench.p13LagrangeBasisValues n problem) (@HighamBench.P13LagrangeProblem.data n problem)
      (@HighamBench.p13Condition
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.p13LagrangeBasisValues n problem) (@HighamBench.P13LagrangeProblem.data n problem)))
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HighamBench.p13Condition
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HighamBench.p13LagrangeBasisValues n problem) (@HighamBench.P13LagrangeProblem.data n problem)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P13Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P13Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Data.Real.Sign`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P13LagrangeProblem`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `562377701dad889128e70e44d1fba16212189deb0fcc416f0e50f0477eb6acad`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.P13LagrangeProblem.data`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2c1cb1ac723fe5842c5417b74edc55ca1e41f7ad186b384c913d21d0cde45304`

Type:

```lean
{n : Nat} → HighamBench.P13LagrangeProblem n → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (self : HighamBench.P13LagrangeProblem n) →
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D003: `HighamBench.p13Condition`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d7fa6d0b4989adc94f4aad1f81cfa4b3701ddea99c39dd03e0dff65ff72bb46d`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (ell f : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ell f =>
  instHDiv.hDiv (Finset.univ.sum fun i => abs (instHMul.hMul (ell i) (f i)))
    (abs (HighamBench.p13InterpolationValue ell f))
```

### D004: `HighamBench.p13IsComponentwiseConditionNumber`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dd85929bdc668e3bda37da906536340fd6d7f6178b17f337d2a104e619f64142`

Type:

```lean
{m : Nat} → (Fin m → Real) → (Fin m → Real) → Real → Prop
```

Fully explicit type:

```lean
{m : Nat} → (ell f : Fin m → Real) → (condition : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} ell f condition =>
  Filter.Tendsto (HighamBench.p13PerturbationSupremum ell f) (nhdsWithin 0 (Set.Ioi 0)) (nhds condition)
```

### D005: `HighamBench.p13LagrangeBasisValues`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4c8c0f61d953c906cfccc20be5b8f72f8cc1ad5ab4cfeec0aa330f65ec1cb4a9`

Type:

```lean
{n : Nat} → HighamBench.P13LagrangeProblem n → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (problem : HighamBench.P13LagrangeProblem n) →
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem => HighamBench.p13LagrangeBasis problem.nodes problem.x
```

### D006: `HighamBench.p13LagrangeValue`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a07b3e9561b3aeb0c88830957317f1b9a4c3fcbacf50db14af14babeca6b0c6a`

Type:

```lean
{n : Nat} → HighamBench.P13LagrangeProblem n → Real
```

Fully explicit type:

```lean
{n : Nat} → (problem : HighamBench.P13LagrangeProblem n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} problem => HighamBench.p13InterpolationValue (HighamBench.p13LagrangeBasisValues problem) problem.data
```

### D007: `HighamBench.P13LagrangeProblem.mk`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `bddc3420dc429a622f81d7d20db97e9f09bdf09e03ca4a21c59b759a8a1760d0`

Type:

```lean
{n : Nat} →
  (nodes : Fin (instHAdd.hAdd n 1) → Real) →
    (Fin (instHAdd.hAdd n 1) → Real) → Real → Function.Injective nodes → HighamBench.P13LagrangeProblem n
```

Fully explicit type:

```lean
{n : Nat} →
  (nodes data :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    (x : Real) →
      (nodes_injective :
          @Function.Injective.{1, 1}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Real nodes) →
        HighamBench.P13LagrangeProblem n
```

### D008: `HighamBench.P13LagrangeProblem.nodes`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `243eb73a9be7a359100369bf6966d19cbfee9ddebe2e766569a8b21116e464fc`

Type:

```lean
{n : Nat} → HighamBench.P13LagrangeProblem n → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (self : HighamBench.P13LagrangeProblem n) →
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D009: `HighamBench.P13LagrangeProblem.x`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `d311025bdf4a5d5934e269c7f30f4e0454421e6b435b03a83160c12868736ac3`

Type:

```lean
{n : Nat} → HighamBench.P13LagrangeProblem n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P13LagrangeProblem n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D010: `HighamBench.p13InterpolationValue`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `70562d0bc0d8c2ac0f383af2d951ff600b8a30ab3a85c099f9d4f449c22ebc0b`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (ell f : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ell f => Finset.univ.sum fun i => instHMul.hMul (ell i) (f i)
```

### D011: `HighamBench.p13LagrangeBasis`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e9c14fd1d77c6af9cd141b376053521b30753f4ea8488be39cf75d199e72d5e6`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Real → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (nodes :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    (x : Real) →
      (j :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} nodes x j =>
  instHDiv.hDiv (Finset.univ.prod fun k => ite (Eq k j) 1 (instHSub.hSub x (nodes k)))
    (Finset.univ.prod fun k => ite (Eq k j) 1 (instHSub.hSub (nodes j) (nodes k)))
```

### D012: `HighamBench.p13PerturbationSupremum`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2422241c118a71798c6e26f7ac7c153680eb92a338b96e69c89a5ed78b4a4973`

Type:

```lean
{m : Nat} → (Fin m → Real) → (Fin m → Real) → Real → Real
```

Fully explicit type:

```lean
{m : Nat} → (ell f : Fin m → Real) → (epsilon : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} ell f epsilon => Real.instSupSet.sSup (HighamBench.p13ScaledPerturbationSet ell f epsilon)
```

### D013: `HighamBench.p13ScaledPerturbationSet`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4c0eeeaae04f91d27ea7c8f92232b80b5d98ecea5ce8d2bea2c1abb9a5316c7e`

Type:

```lean
{m : Nat} → (Fin m → Real) → (Fin m → Real) → Real → Set Real
```

Fully explicit type:

```lean
{m : Nat} → (ell f : Fin m → Real) → (epsilon : Real) → Set.{0} Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} ell f epsilon =>
  setOf fun q =>
    Exists fun deltaF =>
      And (HighamBench.p13DataPerturbation f deltaF epsilon)
        (Eq q (instHDiv.hDiv (HighamBench.p13RelativeInterpolationChange ell f deltaF) epsilon))
```

### D014: `HighamBench.p13DataPerturbation`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `98f8edf762f11b1e3f9c63184f551ffc72a5115ac2d333bfb10331889a0edcea`

Type:

```lean
{m : Nat} → (Fin m → Real) → (Fin m → Real) → Real → Prop
```

Fully explicit type:

```lean
{m : Nat} → (f deltaF : Fin m → Real) → (epsilon : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m} f deltaF epsilon => ∀ (j : Fin m), Real.instLE.le (abs (deltaF j)) (instHMul.hMul epsilon (abs (f j)))
```

### D015: `HighamBench.p13RelativeInterpolationChange`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `f70c36da0e78a5f01be4f388111fc98676b667997a55e2c315f7e53ebe08e085`

Type:

```lean
{m : Nat} → (Fin m → Real) → (Fin m → Real) → (Fin m → Real) → Real
```

Fully explicit type:

```lean
{m : Nat} → (ell f deltaF : Fin m → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} ell f deltaF =>
  instHDiv.hDiv
    (abs
      (instHSub.hSub (HighamBench.p13InterpolationValue ell f)
        (HighamBench.p13InterpolationValue ell (instHAdd.hAdd f deltaF))))
    (abs (HighamBench.p13InterpolationValue ell f))
```

### D016: `And`

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

### D017: `HAdd.hAdd`

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

### D018: `LE.le`

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

### D019: `Nat`

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

### D020: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D021: `OfNat.ofNat`

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

### D022: `One.toOfNat1`

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

### D023: `Real`

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

### D024: `Real.instLE`

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

### D025: `Real.instOne`

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

### D026: `Real.instZero`

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

### D027: `Zero.toOfNat0`

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

### D028: `instAddNat`

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

### D029: `instHAdd`

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

### D030: `instOfNatNat`

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

### D031: `DivInvMonoid.toDiv`

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

### D032: `Filter.Tendsto`

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

### D033: `Fin`

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

### D034: `Fin.fintype`

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

### D035: `Finset.sum`

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

### D036: `Finset.univ`

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

### D037: `HDiv.hDiv`

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

### D038: `HMul.hMul`

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

### D039: `PseudoMetricSpace.toUniformSpace`

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

### D040: `Real.instAddCommMonoid`

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

### D041: `Real.instAddGroup`

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

### D042: `Real.instDivInvMonoid`

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

### D043: `Real.instMul`

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

### D044: `Real.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `896bb94fc15867c0df82ea0f639eb6116e90a24819a66a54db9442e47cba7274`

Type:

```lean
Preorder Real
```

Fully explicit type:

```lean
Preorder.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D045: `Real.lattice`

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

### D046: `Real.pseudoMetricSpace`

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

### D047: `Set.Ioi`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Interval.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ad556a749b4ff2a341c66bd35e0369f79888567fa7730aab8ee2fdd700fbfd52`

Type:

```lean
{α : Type u_1} → [Preorder α] → α → Set α
```

Fully explicit type:

```lean
{α : Type u_1} → [Preorder.{u_1} α] → (b : α) → Set.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Preorder α] b => setOf fun x => inst.lt b x
```

### D048: `UniformSpace.toTopologicalSpace`

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

### D049: `abs`

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

### D050: `instHDiv`

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

### D051: `instHMul`

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

### D052: `nhds`

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

### D053: `nhdsWithin`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.Defs.Filter`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ae7b5c1971244e63e32407fed747da989ad9fef3a4d9c3a64643427eaf071f05`

Type:

```lean
{X : Type u_1} → [TopologicalSpace X] → X → Set X → Filter X
```

Fully explicit type:

```lean
{X : Type u_1} → [TopologicalSpace.{u_1} X] → (x : X) → (s : Set.{u_1} X) → Filter.{u_1} X
```

Definition body (one-level semantic boundary):

```lean
fun {X} [TopologicalSpace X] x s => Filter.instInf.min (nhds x) (Filter.principal s)
```

### D054: `Eq`

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

### D055: `Finset.prod`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e364cffe1f2457eedceca9fe0617d7a66084963ffb6e6ed760d1f3fe74eee841`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [CommMonoid M] s f => (Multiset.map f s.val).prod
```

### D056: `Function.Injective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D057: `HSub.hSub`

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

### D058: `Real.instCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f537dc5e9be2b886066e25d0f560dc52fd1be771759ec3e7b40a5f5f3e6c6467`

Type:

```lean
CommMonoid Real
```

Fully explicit type:

```lean
CommMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D059: `Real.instSub`

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

### D060: `Real.instSupSet`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Archimedean`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `081bbbc44fea5b2cbcd3b5c4d03df40361301523bd4a715fe432385711ce090b`

Type:

```lean
SupSet Real
```

Fully explicit type:

```lean
SupSet.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ sSup := fun s => if h : And s.Nonempty (BddAbove s) then Classical.choose ⋯ else 0 }
```

### D061: `SupSet.sSup`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.SetNotation`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `5b293eab94e25a30827e45bad9ab7fbc70735db9815311e4d67451776240a197`

Type:

```lean
{α : Type u_1} → [self : SupSet α] → Set α → α
```

Fully explicit type:

```lean
{α : Type u_1} → [self : SupSet.{u_1} α] → Set.{u_1} α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SupSet α] => self.1
```

### D062: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D063: `instHSub`

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

### D064: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D065: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D066: `Set`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `a6e551515032966c16e4f42e4548ff1854c2dce05ffe51e98b66943caecc78ec`

Type:

```lean
Type u → Type u
```

Fully explicit type:

```lean
(α : Type u) → Type u
```

Definition body (one-level semantic boundary):

```lean
fun α => α → Prop
```

### D067: `setOf`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cee4433aebd78c308ec85f62ccd30489c00ec9cc23a98f4d2139c17f840f4988`

Type:

```lean
{α : Type u} → (α → Prop) → Set α
```

Fully explicit type:

```lean
{α : Type u} → (p : α → Prop) → Set.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p => p
```

### D068: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D069: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### `HighamBench.P13Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P13Definitions.lean`
SHA-256: `7068b71541b010c612ecd1cceafe4d1b30fe7a0a82bc98ce27a63963cf0f1799`

```lean
import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Sign

namespace HighamBench

open scoped BigOperators

/-- The Lagrange-form value at a fixed evaluation point, with the values of
the Lagrange basis functions supplied as `ell`. -/
noncomputable def p13InterpolationValue {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  ∑ i, ell i * f i

/-- The closed-form quotient on the right-hand side of Lemma 2.2, equation
(2.2). The lemma identifies Definition 2.1's perturbation condition number with
this quantity. -/
noncomputable def p13Condition {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  (∑ i, |ell i * f i|) / |p13InterpolationValue ell f|

/-! ## Exact Lagrange interpolation condition number -/

/-- Fixed data for the degree-`n` interpolation problem in Section 2. There
are exactly `n+1` pairwise distinct nodes, while the evaluation point and nodes
remain fixed under perturbations of `data`. -/
structure P13LagrangeProblem (n : ℕ) where
  nodes : Fin (n + 1) → ℝ
  data : Fin (n + 1) → ℝ
  x : ℝ
  nodes_injective : Function.Injective nodes

/-- The Lagrange basis value `ell_j(x)` from equation (2.1). The skipped
`k = j` factors are represented by `1`. -/
noncomputable def p13LagrangeBasis {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (x : ℝ) (j : Fin (n + 1)) : ℝ :=
  (∏ k : Fin (n + 1), if k = j then 1 else x - nodes k) /
    (∏ k : Fin (n + 1), if k = j then 1 else nodes j - nodes k)

/-- All Lagrange basis values at the fixed evaluation point. -/
noncomputable def p13LagrangeBasisValues {n : ℕ}
    (problem : P13LagrangeProblem n) : Fin (n + 1) → ℝ :=
  p13LagrangeBasis problem.nodes problem.x

/-- The exact degree-`n` interpolant value `p_f(x)` from equation (2.1). -/
noncomputable def p13LagrangeValue {n : ℕ}
    (problem : P13LagrangeProblem n) : ℝ :=
  p13InterpolationValue (p13LagrangeBasisValues problem) problem.data

/-- Definition 2.1's componentwise relative data perturbation
`|delta f| <= epsilon |f|`. -/
def p13DataPerturbation {m : ℕ} (f deltaF : Fin m → ℝ)
    (epsilon : ℝ) : Prop :=
  ∀ j, |deltaF j| ≤ epsilon * |f j|

/-- Relative change in the exact interpolation value caused by `deltaF`.
Definition 2.1 excludes a zero unperturbed value. -/
noncomputable def p13RelativeInterpolationChange {m : ℕ}
    (ell f deltaF : Fin m → ℝ) : ℝ :=
  |p13InterpolationValue ell f - p13InterpolationValue ell (f + deltaF)| /
    |p13InterpolationValue ell f|

/-- The set inside Definition 2.1's supremum at a fixed positive radius. Each
element is the relative output change divided by that radius. -/
def p13ScaledPerturbationSet {m : ℕ} (ell f : Fin m → ℝ)
    (epsilon : ℝ) : Set ℝ :=
  {q | ∃ deltaF : Fin m → ℝ,
    p13DataPerturbation f deltaF epsilon ∧
      q = p13RelativeInterpolationChange ell f deltaF / epsilon}

/-- Definition 2.1's supremum at perturbation radius `epsilon`. -/
noncomputable def p13PerturbationSupremum {m : ℕ}
    (ell f : Fin m → ℝ) (epsilon : ℝ) : ℝ :=
  sSup (p13ScaledPerturbationSet ell f epsilon)

/-- A scalar is Definition 2.1's condition number when the perturbation
suprema tend to it through positive radii. This `Tendsto` formulation records
the equality asserted by the paper without choosing a value for a nonexistent
limit outside the nonzero-value domain. -/
def p13IsComponentwiseConditionNumber {m : ℕ}
    (ell f : Fin m → ℝ) (condition : ℝ) : Prop :=
  Filter.Tendsto (p13PerturbationSupremum ell f)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds condition)

/-- The exact second barycentric formula, with `coeff i = w_i/(x-x_i)`. -/
noncomputable def p13BarycentricValue {n : ℕ}
    (coeff f : Fin n → ℝ) : ℝ :=
  p13InterpolationValue coeff f / p13InterpolationValue coeff (fun _ => 1)

/-- A finite certificate for a computed second barycentric formula: the
numerator terms and denominator terms receive separate additive errors. -/
noncomputable def p13BarycentricComputed {n : ℕ}
    (coeff f deltaNum deltaDen : Fin n → ℝ) : ℝ :=
  (∑ i, (coeff i * f i + deltaNum i)) /
    (∑ i, (coeff i + deltaDen i))

/-- Componentwise relative perturbation of a finite family of terms. -/
def p13TermPerturbation {n : ℕ}
    (v delta : Fin n → ℝ) (epsilon : ℝ) : Prop :=
  ∀ i, |delta i| ≤ epsilon * |v i|

/-! ## The second barycentric formula and its rounding-error execution -/

/-- The reciprocal-product weight (3.2), with the omitted `k = j` factor
represented by `1`. -/
noncomputable def p13DirectBarycentricWeight {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∏ k : Fin (n + 1), if k = j then 1 else nodes j - nodes k)⁻¹

/-- The coefficient `w_j / (x - x_j)` in the second barycentric formula. -/
noncomputable def p13DirectBarycentricCoefficient {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (x : ℝ) (j : Fin (n + 1)) : ℝ :=
  p13DirectBarycentricWeight nodes j / (x - nodes j)

/-- Fixed data for equation (4.1). The real fields are the exact values of the
paper's floating-point inputs; the source does not specify a concrete format. -/
structure P13SecondBarycentricProblem (n : ℕ) where
  nodes : Fin (n + 1) → ℝ
  data : Fin (n + 1) → ℝ
  x : ℝ
  nodes_injective : Function.Injective nodes
  evaluation_off_nodes : ∀ j, x ≠ nodes j

/-- Number of local errors inherited from direct weight computation. -/
def p13WeightCounterLength (n : ℕ) : ℕ := 2 * n

/-- Number of local errors in each numerator term and its summation. -/
def p13NumeratorEvaluationCounterLength (n : ℕ) : ℕ := n + 3

/-- Number of local errors in each denominator term and its summation. -/
def p13DenominatorEvaluationCounterLength (n : ℕ) : ℕ := n + 2

/-- Collected numerator counter in the exact expression before Theorem 4.1. -/
def p13NumeratorCounterLength (n : ℕ) : ℕ := 3 * n + 4

/-- Collected denominator counter in the exact expression before Theorem 4.1. -/
def p13DenominatorCounterLength (n : ℕ) : ℕ := 3 * n + 2

/-- A literal Higham relative-error counter: every local factor is either
`1 + delta` or its reciprocal, and the standard `gamma_k` consequence is
carried as the inherited error-counter lemma used by the paper. -/
structure P13RelativeErrorCounter (u : ℝ) (k : ℕ) where
  value : ℝ
  localError : Fin k → ℝ
  reciprocal : Fin k → Bool
  localError_le : ∀ i, |localError i| ≤ u
  value_eq :
    value = ∏ i, if reciprocal i then (1 + localError i)⁻¹ else 1 + localError i
  gamma_le : GammaValid u k → |value - 1| ≤ gamma u k

/-- A source-level execution certificate for the second barycentric formula.
It retains the shared weight errors, the two evaluation counters, the final
division error, and the two collected counters printed before Theorem 4.1. -/
structure P13SecondBarycentricExecution {n : ℕ}
    (problem : P13SecondBarycentricProblem n) (u : ℝ) where
  u_nonneg : 0 ≤ u
  weightCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13WeightCounterLength n)
  numeratorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13DenominatorEvaluationCounterLength n)
  quotientCounter : P13RelativeErrorCounter u 1
  numeratorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13NumeratorCounterLength n)
  denominatorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13DenominatorCounterLength n)
  weightGammaValid : GammaValid u (p13WeightCounterLength n)
  numeratorEvaluationGammaValid :
    GammaValid u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationGammaValid :
    GammaValid u (p13DenominatorEvaluationCounterLength n)
  quotientGammaValid : GammaValid u 1
  numeratorGammaValid : GammaValid u (p13NumeratorCounterLength n)
  denominatorGammaValid : GammaValid u (p13DenominatorCounterLength n)
  numeratorCounter_eq : ∀ j : Fin (n + 1),
    (numeratorCounter j).value =
      (weightCounter j).value * (numeratorEvaluationCounter j).value *
        quotientCounter.value
  denominatorCounter_eq : ∀ j : Fin (n + 1),
    (denominatorCounter j).value =
      (weightCounter j).value * (denominatorEvaluationCounter j).value

/-- Exact numerator in (4.1). -/
noncomputable def p13SecondBarycentricNumerator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

/-- Exact denominator in (4.1), equivalently the constant-one interpolation
sum used in `cond(x,n,1)`. -/
noncomputable def p13SecondBarycentricDenominator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

/-- Exact value of the second barycentric formula (4.1). -/
noncomputable def p13SecondBarycentricExact {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13SecondBarycentricNumerator problem /
    p13SecondBarycentricDenominator problem

/-- The computed quotient in the paper's uncollected counter form. -/
noncomputable def p13SecondBarycentricComputed {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  ((∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) /
    (∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value *
          (run.denominatorEvaluationCounter j).value)) *
    run.quotientCounter.value

/-- Relative forward error used by Theorem 4.1. -/
noncomputable def p13SecondBarycentricRelativeError {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  |p13SecondBarycentricExact problem - p13SecondBarycentricComputed run| /
    |p13SecondBarycentricExact problem|

/-- The data condition number in Theorem 4.1. -/
noncomputable def p13SecondBarycentricDataCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

/-- The denominator-cancellation condition number `cond(x,n,1)`. -/
noncomputable def p13SecondBarycentricOneCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

/-- Exact finite envelope obtained from the two collected gamma counters. -/
noncomputable def p13SecondBarycentricFiniteEnvelope
    (n : ℕ) (u conditionData conditionOne : ℝ) : ℝ :=
  (gamma u (p13NumeratorCounterLength n) * conditionData +
      gamma u (p13DenominatorCounterLength n) * conditionOne) /
    (1 - gamma u (p13DenominatorCounterLength n) * conditionOne)

/-- The two printed first-order coefficients in equation (4.3), without the
factor `u`. -/
noncomputable def p13SecondBarycentricFirstOrderCoefficient
    (n : ℕ) (conditionData conditionOne : ℝ) : ℝ :=
  (p13NumeratorCounterLength n : ℝ) * conditionData +
    (p13DenominatorCounterLength n : ℝ) * conditionOne

/-- The explicit quadratic-and-higher remainder hidden by `O(u^2)` in (4.3).
The denominator is nonzero in a neighborhood of zero. -/
noncomputable def p13SecondBarycentricForwardRemainder
    (n : ℕ) (conditionData conditionOne u : ℝ) : ℝ :=
  let p : ℝ := p13NumeratorCounterLength n
  let q : ℝ := p13DenominatorCounterLength n
  let A : ℝ := p * conditionData
  let B : ℝ := q * conditionOne
  u ^ 2 *
      (A * p + B * q + A * B + B ^ 2 -
        (A + B) * p * (q + B) * u) /
    ((1 - p * u) * (1 - (q + B) * u))

/-! ## First-order sharpness -/

/-- A realizable first-order counter direction: it is the sum of `k` local
rounding directions, each of magnitude at most one. -/
structure P13FirstOrderCounterDirection (k : ℕ) where
  localDirection : Fin k → ℝ
  localDirection_le_one : ∀ i, |localDirection i| ≤ 1

/-- Total first-order coefficient of a relative-error counter direction. -/
noncomputable def p13FirstOrderCounterDirectionValue {k : ℕ}
    (direction : P13FirstOrderCounterDirection k) : ℝ :=
  ∑ i, direction.localDirection i

/-- Linearized relative forward error of the same four counter stages used by
the exact execution certificate. -/
noncomputable def p13SecondBarycentricFirstOrderResponse {n : ℕ}
    (problem : P13SecondBarycentricProblem n)
    (weightDirection :
      ∀ _j : Fin (n + 1),
        P13FirstOrderCounterDirection (p13WeightCounterLength n))
    (numeratorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13NumeratorEvaluationCounterLength n))
    (denominatorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13DenominatorEvaluationCounterLength n))
    (quotientDirection : P13FirstOrderCounterDirection 1) : ℝ :=
  let coeff := p13DirectBarycentricCoefficient problem.nodes problem.x
  |(∑ j, coeff j * problem.data j *
        (p13FirstOrderCounterDirectionValue (weightDirection j) +
          p13FirstOrderCounterDirectionValue (numeratorDirection j))) /
      p13SecondBarycentricNumerator problem -
    (∑ j, coeff j *
        (p13FirstOrderCounterDirectionValue (weightDirection j) +
          p13FirstOrderCounterDirectionValue (denominatorDirection j))) /
      p13SecondBarycentricDenominator problem +
    p13FirstOrderCounterDirectionValue quotientDirection|

/-- Formal content of the paper's sharpness sentence: realizable local error
directions attain at least one third of the displayed leading coefficient. -/
def P13SecondBarycentricFirstOrderSharp {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : Prop :=
  ∃ (weightDirection :
      ∀ _j : Fin (n + 1),
        P13FirstOrderCounterDirection (p13WeightCounterLength n))
    (numeratorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13NumeratorEvaluationCounterLength n))
    (denominatorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13DenominatorEvaluationCounterLength n))
    (quotientDirection : P13FirstOrderCounterDirection 1),
    (1 / 3 : ℝ) *
        p13SecondBarycentricFirstOrderCoefficient n
          (p13SecondBarycentricDataCondition problem)
          (p13SecondBarycentricOneCondition problem) ≤
      p13SecondBarycentricFirstOrderResponse problem weightDirection
        numeratorDirection denominatorDirection quotientDirection

end HighamBench
```
