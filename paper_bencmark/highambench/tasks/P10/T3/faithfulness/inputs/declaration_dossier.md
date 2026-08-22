# Declaration dossier for P10-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t3_multiplication_via_block_inverse {n : ℕ}
    (hn : 0 < n) (A B : P10Matrix n) :
    P10MultiplicationViaInverse A B
```

## Elaborated target type

```lean
∀ {n : Nat}, instLTNat.lt 0 n → ∀ (A B : HighamBench.P10Matrix n), HighamBench.P10MultiplicationViaInverse A B
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (A B : HighamBench.P10Matrix n), @HighamBench.P10MultiplicationViaInverse n A B
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P10Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P10Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Analysis.SpecialFunctions.Log.Base`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P10Matrix`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4d88fb5bb9dc99cadde8383c8f0b6258d1fba360333ebaa8098421189b8e227f`

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

### D002: `HighamBench.P10MultiplicationViaInverse`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f962a10f1a91c5deb4d3c8142c3aab9f1b7963944803ccf98c86c128d4089d18`

Type:

```lean
{n : Nat} → HighamBench.P10Matrix n → HighamBench.P10Matrix n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P10Matrix n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B =>
  And
    (Eq
      (HighamBench.p10ThreeBlockMul (HighamBench.p10MultiplicationReductionInput A B)
        (HighamBench.p10MultiplicationReductionInverse A B))
      (HighamBench.p10ThreeBlockIdentity n))
    (And
      (Eq
        (HighamBench.p10ThreeBlockMul (HighamBench.p10MultiplicationReductionInverse A B)
          (HighamBench.p10MultiplicationReductionInput A B))
        (HighamBench.p10ThreeBlockIdentity n))
      (Eq (HighamBench.p10MultiplicationReductionInverse A B 0 2) (HighamBench.p10MatMul n A B)))
```

### D003: `HighamBench.P10MultiplicationViaInverse._proof_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `570a103712002fc4ac6da9a16c622ea41fc77c217fe9abe33780d6e65389e986`

Type:

```lean
NeZero (instHAdd.hAdd 2 1)
```

Fully explicit type:

```lean
@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D004: `HighamBench.P10ThreeBlockMatrix`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4c8860f86006ed517187e4f58adfd5bad808824bf861b8747602a6bb909a4989`

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
fun n => Matrix (Fin 3) (Fin 3) (HighamBench.P10Matrix n)
```

### D005: `HighamBench.p10MatMul`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8ad7d3a08ebcc065588b98032ed9256d1069c990b9d1ceee50c8f3a660e436e3`

Type:

```lean
(n : Nat) → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
(n : Nat) → (A B : HighamBench.P10Matrix n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D006: `HighamBench.p10MultiplicationReductionInput`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8cfd71354e4e5f9195239663baf6a9d9db415fdaf00a74a820bdea186feb2f16`

Type:

```lean
{n : Nat} → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10ThreeBlockMatrix n
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P10Matrix n) → HighamBench.P10ThreeBlockMatrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B =>
  EquivLike.toFunLike.coe Matrix.of
    (Matrix.vecCons (Matrix.vecCons 1 (Matrix.vecCons A (Matrix.vecCons 0 Matrix.vecEmpty)))
      (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 (Matrix.vecCons B Matrix.vecEmpty)))
        (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))) Matrix.vecEmpty)))
```

### D007: `HighamBench.p10MultiplicationReductionInverse`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1407b16fad5ca07fa5fd7482bbdbffe0f5d218f46821d61edffdb23396b90eb6`

Type:

```lean
{n : Nat} → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10ThreeBlockMatrix n
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P10Matrix n) → HighamBench.P10ThreeBlockMatrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B =>
  EquivLike.toFunLike.coe Matrix.of
    (Matrix.vecCons
      (Matrix.vecCons 1
        (Matrix.vecCons (Matrix.neg.neg A) (Matrix.vecCons (HighamBench.p10MatMul n A B) Matrix.vecEmpty)))
      (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 1 (Matrix.vecCons (Matrix.neg.neg B) Matrix.vecEmpty)))
        (Matrix.vecCons (Matrix.vecCons 0 (Matrix.vecCons 0 (Matrix.vecCons 1 Matrix.vecEmpty))) Matrix.vecEmpty)))
```

### D008: `HighamBench.p10ThreeBlockIdentity`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f293a759cb9a4af075ed35c37f567f2011a54c7f23e6b8a9a1acb4669b921358`

Type:

```lean
(n : Nat) → HighamBench.P10ThreeBlockMatrix n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P10ThreeBlockMatrix n
```

Definition body (one-level semantic boundary):

```lean
fun n => 1
```

### D009: `HighamBench.p10ThreeBlockMul`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b13676444fef52b278a9ff4743b066f47ae1e4d019f63ddf11ad9c8e2a926c42`

Type:

```lean
{n : Nat} → HighamBench.P10ThreeBlockMatrix n → HighamBench.P10ThreeBlockMatrix n → HighamBench.P10ThreeBlockMatrix n
```

Fully explicit type:

```lean
{n : Nat} → (X Y : HighamBench.P10ThreeBlockMatrix n) → HighamBench.P10ThreeBlockMatrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} X Y => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul X Y
```

### D010: `LT.lt`

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

### D011: `Nat`

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

### D012: `OfNat.ofNat`

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

### D013: `instLTNat`

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

### D014: `instOfNatNat`

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

### D015: `And`

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

### D016: `Eq`

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

### D017: `Fin`

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

### D018: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D019: `Matrix`

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

### D020: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D021: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Fully explicit type:

```lean
{F : Sort u_1} →
  {α : outParam.{u_2 + 1} (Sort u_2)} →
    {β : outParam.{max u_2 (u_3 + 1)} (α → Sort u_3)} → [self : DFunLike.{u_1, u_2, u_3} F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D022: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

Fully explicit type:

```lean
(α : Sort u_1) → (β : Sort u_2) → Sort (max (max 1 u_1) u_2)
```

### D023: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike.{max (max 1 v) u, u, v} (Equiv.{u, v} α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D024: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Fully explicit type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike.{u_1, u_3, u_4} E α β] → FunLike.{u_1, u_3, u_4} E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D025: `Fin.fintype`

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

### D026: `HAdd.hAdd`

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

### D027: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D028: `Matrix.addCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6b893d81bc298230772e16cd0c8ddf7d2638ac0d6127094b06a1290d88f8c3ae`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [AddCommMonoid α] → AddCommMonoid (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} → [AddCommMonoid.{v} α] → AddCommMonoid.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [AddCommMonoid α] => Pi.addCommMonoid
```

### D029: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D030: `Matrix.instMulOfFintypeOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `33a387dd391635ebecd5f0ef20279ffd06b814230ebd7f102ae25fc4475e5bc1`

Type:

```lean
{n : Type u_3} → {α : Type v} → [Fintype n] → [Mul α] → [AddCommMonoid α] → Mul (Matrix n n α)
```

Fully explicit type:

```lean
{n : Type u_3} →
  {α : Type v} → [Fintype.{u_3} n] → [Mul.{v} α] → [AddCommMonoid.{v} α] → Mul.{max v u_3} (Matrix.{u_3, u_3, v} n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [Fintype n] [Mul α] [AddCommMonoid α] =>
  { mul := fun M N => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul M N }
```

### D031: `Matrix.neg`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D032: `Matrix.of`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `2fd11c1f258b666a5be58a830ae21c93bc674ab3014a8a722530d141dddb3638`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Equiv (m → n → α) (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {α : Type v} →
      Equiv.{max (max (u_2 + 1) (u_3 + 1)) (v + 1), max (max (v + 1) (u_3 + 1)) (u_2 + 1)} (m → n → α)
        (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} => Equiv.refl (m → n → α)
```

### D033: `Matrix.one`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b68e4dde96dc7da148aa68eb622604137a0c2dec462b5c39bdd02d8b07d2a59d`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → [One α] → One (Matrix n n α)
```

Fully explicit type:

```lean
{n : Type u_3} →
  {α : Type v} → [DecidableEq.{u_3 + 1} n] → [Zero.{v} α] → [One.{v} α] → One.{max v u_3} (Matrix.{u_3, u_3, v} n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] [One α] => { one := Matrix.diagonal fun x => 1 }
```

### D034: `Matrix.vecCons`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fin.VecNotation`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6d598529744fc7ed189026f2f83ca39c93930021427c51096eca547bc6750a25`

Type:

```lean
{α : Type u} → {n : Nat} → α → (Fin n → α) → Fin n.succ → α
```

Fully explicit type:

```lean
{α : Type u} → {n : Nat} → (h : α) → (t : Fin n → α) → Fin (Nat.succ n) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} h t => Fin.cons h t
```

### D035: `Matrix.vecEmpty`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fin.VecNotation`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `43307adb40ece2d70b6319d8e8f7f5551cf96af32e64c2288a2ca8610f456de1`

Type:

```lean
{α : Type u} → Fin 0 → α
```

Fully explicit type:

```lean
{α : Type u} → Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} => Fin.elim0
```

### D036: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D037: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

Fully explicit type:

```lean
{R : Type u_1} → [Zero.{u_1} R] → (n : R) → Prop
```

### D038: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D039: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

Fully explicit type:

```lean
AddCommMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D041: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D042: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D043: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D044: `Real.instZero`

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

### D045: `Zero.ofOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d610ee8a0a2a61b7850d6032e696e6ae93221da787dff4096e98d4122502f26d`

Type:

```lean
{α : Type u_1} → [OfNat α 0] → Zero α
```

Fully explicit type:

```lean
{α : Type u_1} → [OfNat.{u_1} α (nat_lit 0)] → Zero.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [OfNat α 0] => { zero := 0 }
```

### D046: `Zero.toOfNat0`

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

### D047: `instAddNat`

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

### D048: `instDecidableEqFin`

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

### D049: `instHAdd`

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

### `HighamBench.P10Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P10Definitions.lean`
SHA-256: `0b7d641504c97de374de25cda3e19860a3293f4d60f2d642a0e1eafb1c52975b`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- A square real matrix in the native finite `Matrix` representation. -/
abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite square matrix multiplication. -/
noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

/-- The Frobenius norm, written explicitly to keep the public statement lightweight. -/
noncomputable def p10FrobNorm {n : ℕ} (A : P10Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- An otherwise unspecified matrix norm with the consistency properties used
in the paper's normwise product analysis. -/
structure P10ConsistentMatrixNorm (n : ℕ) where
  value : P10Matrix n → ℝ
  value_nonneg : ∀ A, 0 ≤ value A
  value_eq_zero_iff : ∀ A, value A = 0 ↔ A = 0
  value_smul : ∀ (c : ℝ) A, value (c • A) = |c| * value A
  value_add_le : ∀ A B, value (A + B) ≤ value A + value B
  value_matMul_le : ∀ A B,
    value (p10MatMul n A B) ≤ value A * value B

/-- One stable matrix-product computation with inherited operand errors.  The
cross term and the local higher-order remainder are retained in the execution
model but excluded from its first-order error. -/
structure P10FirstOrderProductRun (n : ℕ) where
  dimension_pos : 0 < n
  matrixNorm : P10ConsistentMatrixNorm n
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mu : ℕ → ℝ
  mu_nonneg : ∀ k, 0 ≤ mu k
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10Matrix n
  rightPerturbation : P10Matrix n
  computedProduct : P10Matrix n
  localFirstOrderError : P10Matrix n
  higherOrderRemainder : P10Matrix n
  leftInheritedError : ℝ
  rightInheritedError : ℝ
  leftInheritedError_nonneg : 0 ≤ leftInheritedError
  rightInheritedError_nonneg : 0 ≤ rightInheritedError
  computed_product :
    computedProduct =
      p10MatMul n
          (exactLeft + leftPerturbation)
          (exactRight + rightPerturbation) +
        localFirstOrderError + higherOrderRemainder
  local_error_bound :
    matrixNorm.value localFirstOrderError ≤
      mu n * epsilon * matrixNorm.value exactLeft * matrixNorm.value exactRight
  left_inherited_error_bound :
    matrixNorm.value leftPerturbation ≤ leftInheritedError
  right_inherited_error_bound :
    matrixNorm.value rightPerturbation ≤ rightInheritedError

/-- The realized product error with the inherited cross term and the local
higher-order remainder removed, exactly as required by first-order analysis. -/
noncomputable def p10FirstOrderProductError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  run.computedProduct - p10MatMul n run.exactLeft run.exactRight -
      p10MatMul n run.leftPerturbation run.rightPerturbation -
    run.higherOrderRemainder

/-- The three first-order contributions printed in equation (8). -/
noncomputable def p10FirstOrderProductErrorBudget {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
      run.matrixNorm.value run.exactRight +
    (run.matrixNorm.value run.exactLeft * run.rightInheritedError +
      run.leftInheritedError * run.matrixNorm.value run.exactRight)

/-- The inherited-right error matrix produced to first order by multiplying
the right operand perturbation on the left by the exact left operand. -/
noncomputable def p10InheritedRightError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.exactLeft run.rightPerturbation

/-- The inherited-left error matrix produced to first order by multiplying
the left operand perturbation by the exact right operand. -/
noncomputable def p10InheritedLeftError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.leftPerturbation run.exactRight

/-- Equation (8)'s local stable-multiplication contribution. -/
noncomputable def p10LocalProductErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
    run.matrixNorm.value run.exactRight

/-- Equation (8)'s inherited-right contribution `||A||*err(B,n)`. -/
noncomputable def p10InheritedRightErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.matrixNorm.value run.exactLeft * run.rightInheritedError

/-- Equation (8)'s inherited-left contribution `err(A,n)*||B||`. -/
noncomputable def p10InheritedLeftErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.leftInheritedError * run.matrixNorm.value run.exactRight

/-- The selected inherited-right term. The first conjunct links all three
first-order matrices to the realized product error; the second gives equation
`(8)`'s `||A||*err(B,n)` bound for the middle matrix. -/
def P10InheritedRightEquation8Term {n : ℕ}
    (run : P10FirstOrderProductRun n) : Prop :=
  p10FirstOrderProductError run =
      run.localFirstOrderError +
        (p10InheritedRightError run + p10InheritedLeftError run) ∧
    run.matrixNorm.value (p10InheritedRightError run) ≤
      p10InheritedRightErrorContribution run

/-! ## Uniform stable-product model for equation (8) -/

/-- A positive machine precision. Quantifying over this type makes the
`O(epsilon^2)` term in the paper's first-order analysis uniform as epsilon
tends to zero through positive values. -/
abbrev P10PositiveEpsilon := {epsilon : ℝ // 0 < epsilon}

/-- One matrix-multiplication algorithm, with the norm and polynomially
bounded stability factor fixed across dimensions, inputs, and precisions. -/
structure P10StableMatrixMultiplication where
  matrixNorm : (n : ℕ) → P10ConsistentMatrixNorm n
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  product : (n : ℕ) → P10PositiveEpsilon →
    P10Matrix n → P10Matrix n → P10Matrix n

/-- An epsilon-indexed family of calls to one stable multiplication
algorithm. The local certificate is equation (1), after absorbing the
first-order change from perturbed operands into one uniform quadratic term.
The inherited errors themselves are required to be uniformly first order. -/
structure P10FirstOrderProductFamily
    (algorithm : P10StableMatrixMultiplication) (n : ℕ) where
  dimension_pos : 0 < n
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10PositiveEpsilon → P10Matrix n
  rightPerturbation : P10PositiveEpsilon → P10Matrix n
  leftInheritedError : P10PositiveEpsilon → ℝ
  rightInheritedError : P10PositiveEpsilon → ℝ
  leftInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ leftInheritedError epsilon
  rightInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ rightInheritedError epsilon
  leftInheritedCoeff : ℝ
  rightInheritedCoeff : ℝ
  leftInheritedCoeff_nonneg : 0 ≤ leftInheritedCoeff
  rightInheritedCoeff_nonneg : 0 ≤ rightInheritedCoeff
  localSecondOrderCoeff : ℝ
  localSecondOrderCoeff_nonneg : 0 ≤ localSecondOrderCoeff
  radius : ℝ
  radius_pos : 0 < radius
  left_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (leftPerturbation epsilon) ≤
      leftInheritedError epsilon
  right_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (rightPerturbation epsilon) ≤
      rightInheritedError epsilon
  left_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    leftInheritedError epsilon ≤ leftInheritedCoeff * (epsilon : ℝ)
  right_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    rightInheritedError epsilon ≤ rightInheritedCoeff * (epsilon : ℝ)
  local_error_bound : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    (algorithm.matrixNorm n).value
        (algorithm.product n epsilon
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon) -
          p10MatMul n
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon)) ≤
      algorithm.mu n * (epsilon : ℝ) *
          (algorithm.matrixNorm n).value exactLeft *
          (algorithm.matrixNorm n).value exactRight +
        localSecondOrderCoeff * (epsilon : ℝ) ^ 2

/-- The actual output of the fixed multiplication algorithm on the two
epsilon-dependent computed operands. -/
noncomputable def p10ProductFamilyComputed {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  algorithm.product n epsilon
    (family.exactLeft + family.leftPerturbation epsilon)
    (family.exactRight + family.rightPerturbation epsilon)

/-- The actual product error. No inherited cross term or local remainder is
removed from this quantity. -/
noncomputable def p10ProductFamilyError {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  p10ProductFamilyComputed algorithm family epsilon -
    p10MatMul n family.exactLeft family.exactRight

/-- The three leading contributions printed in equation (8). -/
noncomputable def p10ProductFamilyErrorBudget {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : ℝ :=
  algorithm.mu n * (epsilon : ℝ) *
      (algorithm.matrixNorm n).value family.exactLeft *
      (algorithm.matrixNorm n).value family.exactRight +
    ((algorithm.matrixNorm n).value family.exactLeft *
        family.rightInheritedError epsilon +
      family.leftInheritedError epsilon *
        (algorithm.matrixNorm n).value family.exactRight)

/-! ## Exact multiplication-to-inversion reduction -/

/-- A three-by-three block matrix whose entries are square real matrices. This
is the block level of the unnumbered display in the proof of Theorem 3.3. -/
abbrev P10ThreeBlockMatrix (n : ℕ) :=
  Matrix (Fin 3) (Fin 3) (P10Matrix n)

/-- The unit upper-triangular block matrix built from the two matrices whose
product is to be recovered by one exact inversion. -/
noncomputable def p10MultiplicationReductionInput {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), A, 0;
     0, 1, B;
     0, 0, 1]

/-- The inverse displayed in the proof of Theorem 3.3. Its upper-right block
is the desired product A times B. -/
noncomputable def p10MultiplicationReductionInverse {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), -A, p10MatMul n A B;
     0, 1, -B;
     0, 0, 1]

/-- Block multiplication for the three-by-three reduction matrices. -/
noncomputable def p10ThreeBlockMul {n : ℕ}
    (X Y : P10ThreeBlockMatrix n) : P10ThreeBlockMatrix n :=
  X * Y

/-- Identity at the three-by-three block level. -/
noncomputable def p10ThreeBlockIdentity (n : ℕ) : P10ThreeBlockMatrix n :=
  1

/-- Exact finite content of the converse reduction in Theorem 3.3: the
printed candidate is a two-sided inverse and its (0,2) block is A times B. -/
def P10MultiplicationViaInverse {n : ℕ} (A B : P10Matrix n) : Prop :=
  p10ThreeBlockMul (p10MultiplicationReductionInput A B)
      (p10MultiplicationReductionInverse A B) =
      p10ThreeBlockIdentity n ∧
    p10ThreeBlockMul (p10MultiplicationReductionInverse A B)
      (p10MultiplicationReductionInput A B) =
      p10ThreeBlockIdentity n ∧
    p10MultiplicationReductionInverse A B (0 : Fin 3) (2 : Fin 3) =
      p10MatMul n A B

end HighamBench
```
