# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ {n : Nat} (A B : LocalDef001 n),
  Real.instLE.le (LocalDef002 (LocalDef003 A B))
    (instHMul.hMul (LocalDef002 A) (LocalDef002 B))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A B : LocalDef001 n),
  @LE.le.{0} Real Real.instLE (@LocalDef002 n (@LocalDef003 n A B))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@LocalDef002 n A)
      (@LocalDef002 n B))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

Type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ba1b58b4e7fdbcda54fe1a9ee4d2ebd9f8d43b80907403bf6ea885fff386083f`

Type:

```lean
{n : Nat} → LocalDef001 n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.frobeniusNormedRing.norm A
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `82a32c03123a1b58cce8a2734d2ddfed6b499db78b5c4e68d56caf8636e3bb0e`

Type:

```lean
{n : Nat} → LocalDef001 n → LocalDef001 n → LocalDef001 n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D004: `HMul.hMul`

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

### D005: `LE.le`

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

### D006: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`

Type:

```lean
Type
```

### D007: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

### D008: `Real.instLE`

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

### D009: `Real.instMul`

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

### D010: `instHMul`

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

### D011: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

### D012: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D013: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D014: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D015: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D016: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`

Type:

```lean
{m : Type u_3} → {α : Type u_5} → [Fintype m] → [RCLike α] → [DecidableEq m] → NormedRing (Matrix m m α)
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

### D017: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D018: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`

Type:

```lean
{α : Type u_5} → [self : NormedRing α] → Norm α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NormedRing α] => self.1
```

### D019: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D020: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`

Type:

```lean
RCLike Real
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

### D021: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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
