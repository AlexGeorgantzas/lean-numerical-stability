# Declaration dossier for P16-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p16_t1_normwise_backward_error_formula {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n)
    (hA : p16IsNonsingular A) (hb : b ≠ 0) :
    IsLeast
      {epsilon : ℝ | p16NormwiseBackwardErrorAdmissible A b xHat epsilon}
      (p16NormalizedResidual A b xHat)
```

## Elaborated target type

```lean
∀ {n : Nat} (A : HighamBench.P16Matrix n) (b xHat : HighamBench.P16Vector n),
  HighamBench.p16IsNonsingular A →
    Ne b 0 →
      IsLeast (setOf fun epsilon => HighamBench.p16NormwiseBackwardErrorAdmissible A b xHat epsilon)
        (HighamBench.p16NormalizedResidual A b xHat)
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A : HighamBench.P16Matrix n) (b xHat : HighamBench.P16Vector n) (hA : @HighamBench.p16IsNonsingular n A)
  (hb :
    @Ne.{1} (HighamBench.P16Vector n) b
      (@OfNat.ofNat.{0} (HighamBench.P16Vector n) (nat_lit 0)
        (@Zero.toOfNat0.{0} (HighamBench.P16Vector n)
          (@Pi.instZero.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instZero)))),
  @IsLeast.{0} Real Real.instLE
    (@setOf.{0} Real fun (epsilon : Real) => @HighamBench.p16NormwiseBackwardErrorAdmissible n A b xHat epsilon)
    (@HighamBench.p16NormalizedResidual n A b xHat)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P16Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P16Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P16Matrix`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D002: `HighamBench.P16Vector`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D003: `HighamBench.p16IsNonsingular`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D004: `HighamBench.p16NormalizedResidual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D005: `HighamBench.p16NormwiseBackwardErrorAdmissible`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `53ace0945f6e54949d81c0b1c487d758f50b1ed44163a2b44ad7ec05a4af9195`

Type:

```lean
{n : Nat} → HighamBench.P16Matrix n → HighamBench.P16Vector n → HighamBench.P16Vector n → Real → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P16Matrix n) → (b xHat : HighamBench.P16Vector n) → (epsilon : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A b xHat epsilon =>
  Exists fun deltaA =>
    Exists fun deltaB =>
      And (Eq (HighamBench.p16MatVec (instHAdd.hAdd A deltaA) xHat) (instHAdd.hAdd b deltaB))
        (And (Real.instLE.le (HighamBench.p16FrobNorm deltaA) (instHMul.hMul epsilon (HighamBench.p16FrobNorm A)))
          (Real.instLE.le (HighamBench.p16VecNorm deltaB) (instHMul.hMul epsilon (HighamBench.p16VecNorm b))))
```

### D006: `HighamBench.p16FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D007: `HighamBench.p16MatVec`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D008: `HighamBench.p16Residual`

- Role: `local`
- Owner module: `HighamBench.P16Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D009: `HighamBench.p16VecNorm`

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

### D010: `Fin`

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

### D011: `IsLeast`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Bounds.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0249f4874cb553374f1701e4c73533c0e111acb582e3b6ddeedb6aa6d521770`

Type:

```lean
{α : Type u_1} → [LE α] → Set α → α → Prop
```

Fully explicit type:

```lean
{α : Type u_1} → [LE.{u_1} α] → (s : Set.{u_1} α) → (a : α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} [LE α] s a => And (Set.instMembership.mem s a) (Set.instMembership.mem (lowerBounds s) a)
```

### D012: `Nat`

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

### D013: `Ne`

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

### D014: `OfNat.ofNat`

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

### D015: `Pi.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D016: `Real`

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

### D017: `Real.instLE`

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

### D018: `Real.instZero`

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

### D019: `Zero.toOfNat0`

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

### D020: `setOf`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D021: `And`

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

### D022: `DivInvMonoid.toDiv`

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

### D023: `Eq`

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

### D024: `Exists`

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

### D025: `Function.Bijective`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D026: `HAdd.hAdd`

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

### D027: `HDiv.hDiv`

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

### D028: `HMul.hMul`

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

### D029: `LE.le`

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

### D030: `Matrix`

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

### D031: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D032: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D033: `Real.instAdd`

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

### D034: `Real.instDivInvMonoid`

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

### D035: `Real.instMul`

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

### D036: `instHAdd`

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

### D037: `instHDiv`

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

### D038: `instHMul`

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

### D039: `Fin.fintype`

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

### D040: `Finset.sum`

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

### D041: `Finset.univ`

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

### D042: `HPow.hPow`

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

### D043: `HSub.hSub`

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

### D044: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D045: `Monoid.toNatPow`

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

### D046: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D047: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D048: `Pi.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D049: `Real.instAddCommMonoid`

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

### D050: `Real.instMonoid`

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

### D051: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D052: `Real.instSub`

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

### D053: `Real.sqrt`

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

### D054: `instDecidableEqFin`

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

### D055: `instHPow`

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

### D056: `instHSub`

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

### D057: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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
