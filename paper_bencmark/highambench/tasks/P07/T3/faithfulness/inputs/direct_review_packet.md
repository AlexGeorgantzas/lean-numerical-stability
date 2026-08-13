# Declaration dossier for P07-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p07_t3_sketch_precondition_condition_certificate
    {m n s : ℕ}
    (QA : Fin m → Fin n → ℝ) (Q C : Fin s → Fin n → ℝ)
    (T : Fin n → Fin n → ℝ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hQA : p07Isometry QA) (hQ : p07Isometry Q)
    (hCT : p07RectMatMul C T = Q)
    (hTsurj : Function.Surjective (p07MatVec T)) :
    (p07ConditionCertificate (p07RectMatMul QA T) α β ↔
      p07ConditionCertificate C β⁻¹ α⁻¹) ∧
      β / α = α⁻¹ / β⁻¹
```

## Elaborated target type

```lean
∀ {m n s : Nat} (QA : Fin m → Fin n → Real) (Q C : Fin s → Fin n → Real) (T : Fin n → Fin n → Real) (α β : Real),
  Real.instLT.lt 0 α →
    Real.instLT.lt 0 β →
      HighamBench.p07Isometry QA →
        HighamBench.p07Isometry Q →
          Eq (HighamBench.p07RectMatMul C T) Q →
            Function.Surjective (HighamBench.p07MatVec T) →
              And
                (Iff (HighamBench.p07ConditionCertificate (HighamBench.p07RectMatMul QA T) α β)
                  (HighamBench.p07ConditionCertificate C (Real.instInv.inv β) (Real.instInv.inv α)))
                (Eq (instHDiv.hDiv β α) (instHDiv.hDiv (Real.instInv.inv α) (Real.instInv.inv β)))
```

## Fully explicit elaborated target type

```lean
∀ {m n s : Nat} (QA : Fin m → Fin n → Real) (Q C : Fin s → Fin n → Real) (T : Fin n → Fin n → Real) (α β : Real)
  (hα : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) α)
  (hβ : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) β)
  (hQA : @HighamBench.p07Isometry m n QA) (hQ : @HighamBench.p07Isometry s n Q)
  (hCT : @Eq.{1} (Fin s → Fin n → Real) (@HighamBench.p07RectMatMul s n n C T) Q)
  (hTsurj : @Function.Surjective.{1, 1} (Fin n → Real) (Fin n → Real) (@HighamBench.p07MatVec n n T)),
  And
    (Iff (@HighamBench.p07ConditionCertificate m n (@HighamBench.p07RectMatMul m n n QA T) α β)
      (@HighamBench.p07ConditionCertificate s n C (@Inv.inv.{0} Real Real.instInv β)
        (@Inv.inv.{0} Real Real.instInv α)))
    (@Eq.{1} Real
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) β
        α)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Inv.inv.{0} Real Real.instInv α) (@Inv.inv.{0} Real Real.instInv β)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P07Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P07Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p07ConditionCertificate`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `dea4d285d9d489c8bd39eb2e4dc2993887236d009ec667479046e336a874c961`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Real → Real → Prop
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (lower upper : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A lower upper => And (HighamBench.p07RectLowerBound A lower) (HighamBench.p07RectOpNorm2Le A upper)
```

### D002: `HighamBench.p07Isometry`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D003: `HighamBench.p07MatVec`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `c20ee94e8dfa7a21c0972744b89ff2650d7462ecb441662c2e1930d980ab8dc5`
- Reuse SHA-256: `2c57ade87344bcd23c15d60d29e08d8e736d0b39921a84f5f6eae43a2cebef3c`

Hash-verified prior interpretation:

For an m-by-n real array A and n-vector x, this returns the m-vector whose i-th entry is the finite sum of A i j times x j.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p07RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D005: `HighamBench.p07RectLowerBound`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D006: `HighamBench.p07RectOpNorm2Le`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D007: `HighamBench.p07VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P07Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `9ab663fe9a74061006c9976250ea5e93003df8c9f220f04dff6f950bb66a0ff4`
- Reuse SHA-256: `7b95691578028c3cbc7bdfea5d3bf7a47abc942b755f9b237c7c74cbb6bf2862`

Hash-verified prior interpretation:

This is the Euclidean vector 2-norm, the square root of the sum of the squares of all coordinates.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `And`

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

### D009: `DivInvMonoid.toDiv`

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

### D010: `Eq`

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

### D011: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `f53009fa223bbdaf32a11aabafd6ae3905217db5e5485a58ba85a5a9bbeabf26`

Hash-verified prior interpretation:

Fin n is the finite coordinate type with n elements indexed from zero through n minus one.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Function.Surjective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `445be13b68e9dc4df2e669e26d66cfeb452be0838a57a48f28fe13bacbab89c0`

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
fun {α} {β} f => ∀ (b : β), Exists fun a => Eq (f a) b
```

### D013: `HDiv.hDiv`

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

### D014: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D015: `Inv.inv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D016: `LT.lt`

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

Fully explicit type:

```lean
Type
```

### D018: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `9f4ae78e268f549f9fa054e8a40dc22788e317dd074a667cdbf8b9f9a04c9e0f`

Hash-verified prior interpretation:

This interprets a natural-number literal in the requested type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `0494ec48a9b90eb653272c5d824dd315471ba96930fec5ed804c46889b610589`

Hash-verified prior interpretation:

Real is Lean's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instDivInvMonoid`

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

### D021: `Real.instInv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D022: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`
- Reuse SHA-256: `0d44ef95aa16c59ef5741df72c24c4669439153723e4598a5313fba5464896ee`

Hash-verified prior interpretation:

This is the standard strict linear order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.instZero`

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

Fully explicit type:

```lean
{α : Type u_1} → [Zero.{u_1} α] → OfNat.{u_1} α (nat_lit 0)
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D025: `instHDiv`

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

### D026: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `39d9783de210591165f8499841e03d99a0a0b62255eb37f35a73bb01a49c2398`

Hash-verified prior interpretation:

This provides the finite enumeration of every element of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `a63cd30eebffc4e76d0571b9ebf5db7feee1cfd30b57b048e28ebe78c96ac2cf`

Hash-verified prior interpretation:

This forms the finite additive sum of a function over a finite set.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `8d3033a348432d628aa39091e52f7667d26e9f28843d61f06169d3818f9bc98c`

Hash-verified prior interpretation:

This is the finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `1762e1a6d37464af56133510a8e2f8d2d3a2f73f280ffc8c3b9782bc83c4f5db`

Hash-verified prior interpretation:

This dispatches the selected heterogeneous multiplication operation, which here is ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `2436f37fe5f5b335500c23bb11b11d3cd2846daac0a0cf97783d3ecaa14c4a74`

Hash-verified prior interpretation:

This supplies real addition, zero, associativity, commutativity, and identity laws to finite sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `b5ca9ce66e8e0587bfc928482989109c5e9fb5d61c08cd29b8cd647786c9f0bb`

Hash-verified prior interpretation:

This is ordinary multiplication on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `82fca9b6c172b8aeabc0990e33296f4c8cefd3de30cc36f77b5ad630a722f8aa`

Hash-verified prior interpretation:

This lifts a homogeneous Mul instance to heterogeneous-multiplication notation with the same input and output type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `952e5795ef7760dad834bbcc3b861fae368185e0dd6070f16dd7164291a4fc5b`

Hash-verified prior interpretation:

This dispatches exponentiation, here raising a real coordinate to a natural-number power.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `1d6c5538d176983f9f66a5e8b158177e8e77312bfb5c479547f1aa6803644b14`

Hash-verified prior interpretation:

This dispatches the selected non-strict order relation, which here is real less-than-or-equal.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `a177366079d99333be27eafbc37babf4ee79482cd37f3837ae3662025699994f`

Hash-verified prior interpretation:

This supplies natural-number powers from repeated multiplication in a monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `2ed855b976956890f6711c98a5bc63a243beeefa08dc5896af2afad348a74bd8`

Hash-verified prior interpretation:

This is the standard non-strict order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `5ecabffed05500c8ce16d7e7757c9f1a4b160004e0f0616f03a7ddefa43f8efa`

Hash-verified prior interpretation:

This supplies real multiplication, one, and natural powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `0817c22961009afbc31736125fe57848bc41bcfcd5f650dab32ca6cb7a9331fd`

Hash-verified prior interpretation:

This is the nonnegative real square-root function.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `8957e4a97b00059c55dc6f45409d20d173c0b722eca8c932ec27934e2b6c0331`

Hash-verified prior interpretation:

This lifts a Pow instance to heterogeneous-power notation while retaining the same base and result type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `9fa32deaa97ab2beed5a53804c107f2ed5a722fbf240731dd537975f9920a6b9`

Hash-verified prior interpretation:

This interprets each natural-number literal as that same natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
