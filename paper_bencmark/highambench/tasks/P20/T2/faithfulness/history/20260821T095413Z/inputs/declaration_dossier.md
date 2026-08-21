# Declaration dossier for P20-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p20_t2_accumulation_underflow_le_input {m n q : ℕ}
    (theta gmin Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ)
    (htheta : 1 ≤ theta) (hGmin : 0 ≤ Gmin) (hGg : Gmin ≤ gmin) :
    p20SingleAccumUnderflowBound theta Gmin A B ≤
      p20SingleInputUnderflowBound theta gmin A B
```

## Elaborated target type

```lean
∀ {m n q : Nat} (theta gmin Gmin : Real) (A : Fin m → Fin n → Real) (B : Fin n → Fin q → Real),
  Real.instLE.le 1 theta →
    Real.instLE.le 0 Gmin →
      Real.instLE.le Gmin gmin →
        Real.instLE.le (HighamBench.p20SingleAccumUnderflowBound theta Gmin A B)
          (HighamBench.p20SingleInputUnderflowBound theta gmin A B)
```

## Fully explicit elaborated target type

```lean
∀ {m n q : Nat} (theta gmin Gmin : Real) (A : Fin m → Fin n → Real) (B : Fin n → Fin q → Real)
  (htheta : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) theta)
  (hGmin : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Gmin)
  (hGg : @LE.le.{0} Real Real.instLE Gmin gmin),
  @LE.le.{0} Real Real.instLE (@HighamBench.p20SingleAccumUnderflowBound m n q theta Gmin A B)
    (@HighamBench.p20SingleInputUnderflowBound m n q theta gmin A B)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P20Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P20Definitions` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Real.Sqrt`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p20SingleAccumUnderflowBound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `424faa44feb9fbd81521978e0b336914e4a087bca743a8d6e2f370a578cc4f5c`

Type:

```lean
{m n q : Nat} → Real → Real → (Fin m → Fin n → Real) → (Fin n → Fin q → Real) → Real
```

Fully explicit type:

```lean
{m n q : Nat} → (theta Gmin : Real) → (A : Fin m → Fin n → Real) → (B : Fin n → Fin q → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q} theta Gmin A B =>
  instHMul.hMul
    (instHMul.hMul
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 4 (instHPow.hPow n.cast 2)) (instHPow.hPow (Real.instInv.inv theta) 2)) Gmin)
      (HighamBench.p20InfNormRect A))
    (HighamBench.p20InfNormRect B)
```

### D002: `HighamBench.p20SingleInputUnderflowBound`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cb465e8866dd7c5ba75fc60b9e5548482bc55d09221828ea20a8443b6a687402`

Type:

```lean
{m n q : Nat} → Real → Real → (Fin m → Fin n → Real) → (Fin n → Fin q → Real) → Real
```

Fully explicit type:

```lean
{m n q : Nat} → (theta gmin : Real) → (A : Fin m → Fin n → Real) → (B : Fin n → Fin q → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n q} theta gmin A B =>
  instHMul.hMul
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (instHMul.hMul 4 (instHPow.hPow n.cast 2)) (Real.instInv.inv theta)) gmin)
      (HighamBench.p20InfNormRect A))
    (HighamBench.p20InfNormRect B)
```

### D003: `HighamBench.p20InfNormRect`

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

### D004: `HighamBench.p20SingleInputUnderflowBound._proof_1`

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

### D005: `Fin`

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

### D006: `LE.le`

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

### D007: `Nat`

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

### D008: `OfNat.ofNat`

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

### D009: `One.toOfNat1`

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

### D010: `Real`

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

### D011: `Real.instLE`

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

### D012: `Real.instOne`

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

### D013: `Real.instZero`

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

### D014: `Zero.toOfNat0`

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

### D015: `HMul.hMul`

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

### D016: `HPow.hPow`

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

### D017: `Inv.inv`

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

### D018: `Monoid.toNatPow`

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

### D019: `Nat.cast`

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

### D020: `Real.instInv`

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

### D021: `Real.instMonoid`

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

### D022: `Real.instMul`

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

### D023: `Real.instNatCast`

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

### D024: `instHMul`

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

### D025: `instHPow`

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

### D026: `instOfNatAtLeastTwo`

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

### D027: `instOfNatNat`

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

### D028: `ConditionallyCompleteLinearOrderBot.toOrderBot`

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

### D029: `Fin.fintype`

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

### D030: `Finset.sum`

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

### D031: `Finset.sup`

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

### D032: `Finset.univ`

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

### D033: `HAdd.hAdd`

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

### D034: `NNNorm.nnnorm`

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

### D035: `NNReal`

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

### D036: `NNReal.instConditionallyCompleteLinearOrderBot`

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

### D037: `NNReal.toReal`

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

### D038: `Nat.AtLeastTwo`

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

### D039: `NonAssocSemiring.toNonUnitalNonAssocSemiring`

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

### D040: `NonUnitalNonAssocSemiring.toAddCommMonoid`

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

### D041: `NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing`

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

### D042: `NonUnitalSeminormedRing.toSeminormedAddCommGroup`

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

### D043: `NormedCommRing.toSeminormedCommRing`

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

### D044: `Real.normedCommRing`

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

### D045: `SeminormedAddCommGroup.toSeminormedAddGroup`

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

### D046: `SeminormedAddGroup.toNNNorm`

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

### D047: `SeminormedCommRing.toNonUnitalSeminormedCommRing`

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

### D048: `Semiring.toNonAssocSemiring`

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

### D049: `instAddNat`

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

### D050: `instHAdd`

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

### D051: `instSemilatticeSupNNReal`

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

### D052: `instSemiringNNReal`

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
SHA-256: `33554be89414f9d3fa27232131e6817fcc7f2017087e8bae4f59ceb4e2cfa4ea`

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

end HighamBench
```
