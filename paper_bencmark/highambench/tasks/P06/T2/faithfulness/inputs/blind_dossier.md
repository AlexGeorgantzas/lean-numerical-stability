# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {m n : Nat} (M : Fin m → Fin n → Real) (L : Real),
  Real.instLE.le 0 L →
    Iff (LocalDef003 M L)
      (LocalDef002 (LocalDef004 M) fun a b =>
        instHMul.hMul L (LocalDef001 a b))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (M : Fin m → Fin n → Real) (L : Real)
  (hL : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) L),
  Iff (@LocalDef003 m n M L)
    (@LocalDef002.{0} (Sum.{0, 0} (Fin m) (Fin n))
      (@instFintypeSum.{0, 0} (Fin m) (Fin n) (Fin.fintype m) (Fin.fintype n))
      (@LocalDef004 m n M) fun (a b : Sum.{0, 0} (Fin m) (Fin n)) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) L
        (@LocalDef001.{0} (Sum.{0, 0} (Fin m) (Fin n))
          (fun (a b : Sum.{0, 0} (Fin m) (Fin n)) =>
            @instDecidableEqSum.{0, 0} (Fin m) (Fin n) (instDecidableEqFin m) (instDecidableEqFin n) a b)
          a b))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a9037c406664bfc13b1a434dbaf41ca104afd808a9ca85949e0dd52361ad6016`

Type:

```lean
{ι : Type u_1} → [DecidableEq ι] → ι → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [DecidableEq ι] i j => ite (Eq i j) 1 0
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `29fd5e4651ff034b2867e2a0fe108ffa9a89079e677bf93faf1d5cc013262247`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → ι → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A B =>
  ∀ (x : ι → Real), Real.instLE.le (LocalDef005 A x) (LocalDef005 B x)
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2f0f3a599fcba43fced25539e0ee05f966cef66bd1dec61d355e81e51e2bc1f9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A L =>
  ∀ (x : Fin n → Real),
    Real.instLE.le (LocalDef008 (LocalDef006 A x)) (instHMul.hMul L (LocalDef008 x))
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `53cc5f88a60adb56cc8442c818fa36d8fc6c9a59e3f9b6dd70ba3ca237853a83`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} M a b =>
  LocalDef007 (fun a b => Real) a b (fun i j => M i j) (fun j i => M i j) fun x x_1 => 0
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b2a3caa2b131aec4750b821fb5fdc5ebe3b4978680b79a022718f9a3ff57923b`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A x => Finset.univ.sum fun i => instHMul.hMul (x i) (LocalDef009 A x i)
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `893dee110847631319ce412fdc634324446f2cfd73af2c3a356c467875edecc9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2e93fce8941b11aab9fae216b0f8967e24e11858f44e61127d4d4d4b625dec34`

Type:

```lean
{m n : Nat} →
  (motive : Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n) → Sort u_1) →
    (a b : Sum (Fin m) (Fin n)) →
      ((i : Fin m) → (j : Fin n) → motive (Sum.inl i) (Sum.inr j)) →
        ((j : Fin n) → (i : Fin m) → motive (Sum.inr j) (Sum.inl i)) →
          ((x x_1 : Sum (Fin m) (Fin n)) → motive x x_1) → motive a b
```

Definition body (one-level semantic boundary):

```lean
fun {m n} motive a b h_1 h_2 h_3 =>
  Sum.casesOn a
    (fun val =>
      LocalDef010 b (fun val_1 => h_1 val val_1) fun h => h_3 (Sum.inl val) b)
    fun val =>
    LocalDef011 b (fun val_1 => h_2 val val_1) fun h => h_3 (Sum.inr val) b
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `641a08c9509bcfec9f54c8dcf330d38cf5a97f59688d88c388269019be35f39d`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => (Finset.univ.sum fun i => instHPow.hPow (x i) 2).sqrt
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b24fc73f1af2f6391e5db4a099c98a3db898d965bdf2719166452e6ff5e904a8`

Type:

```lean
{ι : Type u_1} → [Fintype ι] → (ι → ι → Real) → (ι → Real) → ι → Real
```

Definition body (one-level semantic boundary):

```lean
fun {ι} [Fintype ι] A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `3c429f9ecaacc60087da2dc77ae1606f32a23d9f1f6b9ee7253a96bb2452101d`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : β) → motive (Sum.inr val)) → (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inr =>
  Sum.rec (motive := fun t => (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t) (fun val «else» => «else» ⋯)
    (fun val «else» => inr val) t
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `cadeae4b49c6aacf73024f8587ace0c7734c9e74602f2cb19cf7879cd1dca94c`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : α) → motive (Sum.inl val)) → (Nat.hasNotBit 1 t.ctorIdx → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inl =>
  Sum.rec (motive := fun t => (Nat.hasNotBit 1 t.ctorIdx → motive t) → motive t) (fun val «else» => inl val)
    (fun val «else» => «else» ⋯) t
```

### D012: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D013: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D014: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D015: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

### D016: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D017: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D018: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D019: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D020: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D021: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`

Type:

```lean
Mul Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D022: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D023: `Sum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b918d4b75e8964578622cc8220c8e47d62bd100bdf794f538778ce95c76f70c6`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D024: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D025: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D026: `instDecidableEqSum`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e82c0dc84549c649cd05cd11dc0a7647cdf8009b36bcf62a4387ebc229f9d316`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [DecidableEq α] → [DecidableEq β] → DecidableEq (Sum α β)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] [DecidableEq β] => instDecidableEqSum.decEq
```

### D027: `instFintypeSum`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Sum`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `26993d4e890c6ac0fc8a0a76b602ea044068841a7430282875d3fa3c6e1638b5`

Type:

```lean
(α : Type u) → (β : Type v) → [Fintype α] → [Fintype β] → Fintype (Sum α β)
```

Definition body (one-level semantic boundary):

```lean
fun α β [Fintype α] [Fintype β] => { elems := Finset.univ.disjSum Finset.univ, complete := ⋯ }
```

### D028: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D029: `DecidableEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `ceb5edcca38a0d8e0cbe42efd319eed4e877a75211690cacfd89ee5799fb1004`

Type:

```lean
Sort u → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun α => (a b : α) → Decidable (Eq a b)
```

### D030: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D031: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

### D032: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D033: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D034: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D035: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D036: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D037: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D038: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D039: `Nat.hasNotBit`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7699bcfbcaba03b7e3c810ec7a92e896502b1469cf1fc5b0a64fe91880a756fd`

Type:

```lean
Nat → Nat → Prop
```

Definition body (one-level semantic boundary):

```lean
fun m n => Ne (Nat.land 1 (m.shiftRight n)) 1
```

### D040: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D041: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D042: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`

Type:

```lean
Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun x => ((instFunLikeOrderIso NNReal NNReal).coe NNReal.sqrt x.toNNReal).toReal
```

### D043: `Sum.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `7674fe9612b87e143d023c1d08d4603d6cf1f13a165277c77c0c3c17ab768682`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      (t : Sum α β) → ((val : α) → motive (Sum.inl val)) → ((val : β) → motive (Sum.inr val)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {motive} t inl inr => Sum.rec (fun val => inl val) (fun val => inr val) t
```

### D044: `Sum.ctorIdx`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f2e8ea052f4671bb35c4cb334f4c653780658af219b1b860c094b6edf670d102`

Type:

```lean
{α : Type u} → {β : Type v} → Sum α β → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} x => Sum.casesOn x (fun val => 0) fun val => 1
```

### D045: `Sum.inl`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `1a4aaa4b5e1935c80236f326430592c895be07047c023475286fc160cbbfdb60`

Type:

```lean
{α : Type u} → {β : Type v} → α → Sum α β
```

### D046: `Sum.inr`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `5fe7cba3f12df2d7f7efb2b320c8dd9ff78fdbfb0267e92f2e571c99d2f1e6f1`

Type:

```lean
{α : Type u} → {β : Type v} → β → Sum α β
```

### D047: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D048: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D049: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

### D050: `Bool.false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `903a7293b3a1c2eca38e3f5e4346c7e732c386d96e6399ffb0cedaba068cd441`

Type:

```lean
Bool
```

### D051: `Eq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `62d4020b7012db70e44624c7d64dd267524e7e75e4b869680e0c95d2231c85d1`

Type:

```lean
∀ {α : Sort u_1} (a : α), Eq a a
```

### D052: `Nat.land`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `ba03bca5cd1935764fe2e7cb6539b6c860f3eb526cb9c7b1f6e16d6eabb9ff7d`

Type:

```lean
Nat → Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.bitwise Bool.and
```

### D053: `Nat.ne_of_beq_eq_false`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `5d02d2e9f1cc8cdfa62b0caf31b9843167d35f0b8445d653452912a5f56fd1ee`

Type:

```lean
∀ {n m : Nat}, Eq (n.beq m) Bool.false → Not (Eq n m)
```

### D054: `Nat.shiftRight`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Bitwise.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `83adfdc344d13b726e9b2aa74662fceecc7cda9ef92d8b83bff3d2058a7ee7a6`

Type:

```lean
Nat → Nat → Nat
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  Nat.brecOn (motive := fun x => Nat → Nat) x_1
    (fun x f x_2 =>
      Nat.shiftLeft.match_1 (fun x x_3 => Nat.below (motive := fun x => Nat → Nat) x_3 → Nat) x_2 x (fun n x => n)
        (fun n m x => instHDiv.hDiv (x.1 n) 2) f)
    x
```

### D055: `Sum.rec`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `recursor`
- Distance from target type: `4`
- Semantic SHA-256: `3ccfe56c135565c27c454b52bb1960295625b2148cd6d2a03f85045c566e3488`

Type:

```lean
{α : Type u} →
  {β : Type v} →
    {motive : Sum α β → Sort u_1} →
      ((val : α) → motive (Sum.inl val)) → ((val : β) → motive (Sum.inr val)) → (t : Sum α β) → motive t
```
