# Declaration dossier for P10-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t2_product_error_with_cross_term {n : ℕ}
    (A dA B dB E : P10Matrix n) :
    p10FrobNorm (p10ProductErrorExpansion n A dA B dB E) ≤
      p10FrobNorm E +
        p10FrobNorm A * p10FrobNorm dB +
        p10FrobNorm dA * p10FrobNorm B +
        p10FrobNorm dA * p10FrobNorm dB
```

## Elaborated target type

```lean
∀ {n : Nat} (A dA B dB E : HighamBench.P10Matrix n),
  Real.instLE.le (HighamBench.p10FrobNorm (HighamBench.p10ProductErrorExpansion n A dA B dB E))
    (instHAdd.hAdd
      (instHAdd.hAdd
        (instHAdd.hAdd (HighamBench.p10FrobNorm E)
          (instHMul.hMul (HighamBench.p10FrobNorm A) (HighamBench.p10FrobNorm dB)))
        (instHMul.hMul (HighamBench.p10FrobNorm dA) (HighamBench.p10FrobNorm B)))
      (instHMul.hMul (HighamBench.p10FrobNorm dA) (HighamBench.p10FrobNorm dB)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A dA B dB E : HighamBench.P10Matrix n),
  @LE.le.{0} Real Real.instLE (@HighamBench.p10FrobNorm n (HighamBench.p10ProductErrorExpansion n A dA B dB E))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p10FrobNorm n E)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p10FrobNorm n A)
            (@HighamBench.p10FrobNorm n dB)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p10FrobNorm n dA)
          (@HighamBench.p10FrobNorm n B)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@HighamBench.p10FrobNorm n dA)
        (@HighamBench.p10FrobNorm n dB)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P10Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P10Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

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

### D002: `HighamBench.p10FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `218361ae17724218614c78ea7e60ed59909b1d6fafeab7842a25909187cad311`

Type:

```lean
{n : Nat} → HighamBench.P10Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P10Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D003: `HighamBench.p10ProductErrorExpansion`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `981d8836596733ef7334b647340b02dc096bf145329b1ab6cb6eeeb31f21ee52`

Type:

```lean
(n : Nat) →
  HighamBench.P10Matrix n →
    HighamBench.P10Matrix n →
      HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
(n : Nat) → (A dA B dB E : HighamBench.P10Matrix n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n A dA B dB E =>
  instHAdd.hAdd E
    (instHAdd.hAdd (HighamBench.p10MatMul n A dB)
      (instHAdd.hAdd (HighamBench.p10MatMul n dA B) (HighamBench.p10MatMul n dA dB)))
```

### D004: `HighamBench.p10MatMul`

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

### D005: `HAdd.hAdd`

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

### D006: `HMul.hMul`

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

### D007: `LE.le`

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

### D008: `Nat`

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

### D009: `Real`

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

### D010: `Real.instAdd`

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

### D012: `Real.instMul`

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

### D013: `instHAdd`

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

### D014: `instHMul`

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

### D015: `Fin`

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

### D016: `Fin.fintype`

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

### D017: `Finset.sum`

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

### D018: `Finset.univ`

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

### D019: `HPow.hPow`

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

### D020: `Matrix`

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

### D021: `Matrix.add`

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

### D022: `Monoid.toNatPow`

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

### D023: `OfNat.ofNat`

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

### D024: `Real.instAddCommMonoid`

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

### D025: `Real.instMonoid`

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

### D026: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D027: `instHPow`

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

### D028: `instOfNatNat`

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
SHA-256: `fe10c0868a161a26b4cd39e18b9dd21121fff955cca9888d7b854960cae02671`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

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

/-- Exact computed product with inherited input perturbations and a local product error. -/
noncomputable def p10PerturbedProduct (n : ℕ)
    (A dA B dB E : P10Matrix n) : P10Matrix n :=
  p10MatMul n (A + dA) (B + dB) + E

/-- The exact local, inherited-left, inherited-right, and cross-term error expansion. -/
noncomputable def p10ProductErrorExpansion (n : ℕ)
    (A dA B dB E : P10Matrix n) : P10Matrix n :=
  E + (p10MatMul n A dB +
    (p10MatMul n dA B + p10MatMul n dA dB))

/-- The one-level amplification factor in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterGrowth {n : ℕ}
    (A B : P10Matrix n) (sep : ℝ) : ℝ :=
  4 + 2 * (p10FrobNorm A + p10FrobNorm B) / sep

/-- The one-level forcing term in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterForcing {n : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ) : ℝ :=
  epsilon / sep *
    (3 * p10FrobNorm C +
      2 * mu * (p10FrobNorm A + p10FrobNorm B) * p10FrobNorm R)

end HighamBench
```
