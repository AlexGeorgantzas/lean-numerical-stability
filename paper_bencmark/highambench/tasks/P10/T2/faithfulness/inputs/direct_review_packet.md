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
- Semantic SHA-256: `4d88fb5bb9dc99cadde8383c8f0b6258d1fba360333ebaa8098421189b8e227f`
- Reuse SHA-256: `7bbb140588b0cbe60838fa3a730653d5e3db50aa2d82c7f07dd98f4cd02166c8`

Hash-verified prior interpretation:

For each natural number n, this is definitionally the type Matrix (Fin n) (Fin n) Real, namely square n-by-n real matrices.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D002: `HighamBench.p10FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `218361ae17724218614c78ea7e60ed59909b1d6fafeab7842a25909187cad311`
- Reuse SHA-256: `f0913e4a3cb61ed7354bd6a8d663bbd8b2c93ae29427d84803fab115a0397e5f`

Hash-verified prior interpretation:

This maps a real matrix to the square root of the sum of the squares of all its entries, so it is the unsquared Frobenius norm.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `8ad7d3a08ebcc065588b98032ed9256d1069c990b9d1ceee50c8f3a660e436e3`
- Reuse SHA-256: `94ffe85de2416b997a7c4803656fb0728a0feec92ae804e31d097e40942fdf52`

Hash-verified prior interpretation:

This is ordinary matrix multiplication supplied by the matrix HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `26ec858b7914040b62e41dac07549d0e710576ebffcab48ae340f110ef32e4ad`

Hash-verified prior interpretation:

This projects the heterogeneous multiplication operation from the applicable HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `30a6ffc7f69a075cd10e87a2d586237b1dc7098e4c686f0874110b84179c4b55`

Hash-verified prior interpretation:

This projects the binary non-strict order relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `519df6688320448028db3a6368518c22853de54ad47b45d39946022a1e1bdf87`

Hash-verified prior interpretation:

This is the inductive type of natural numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `901954785acc1690e69168c413434be73549452178ff230777d608e0a5c1c72a`

Hash-verified prior interpretation:

This is the mathematical real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `1a7b1542350a021093ae24fdcaf462b9362f6c48f6f02fff171623ea4471b7c1`

Hash-verified prior interpretation:

This equips Real with its usual non-strict order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `7ee4e8807313f6dcf59b99b52940f5cd8eb868799c0b55b8b7ce1b1745581ea7`

Hash-verified prior interpretation:

This equips Real with ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `e59d6740ce08cc0daa448ab94b648895253d68ac0e9c1eddcd501b2207170f14`

Hash-verified prior interpretation:

This converts a homogeneous Mul instance into the corresponding homogeneous HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `cf0e0c079b128caed6b4d65311a6841c6e5632ce09e2aa0f9fb215fea4607413`

Hash-verified prior interpretation:

Fin n is the finite index type whose values correspond to the integers from zero through n minus one.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `a3999a1876b4d406154453fec4f9ac4d68c8269ece8a353478f85850c47b023c`

Hash-verified prior interpretation:

This supplies a finite enumeration of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `de6d317f3a880f3f1114792c82569d34742d40bae7422a3e5db0b5805b28d019`

Hash-verified prior interpretation:

This forms the additive sum of a function over a finite set.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `5d4d7dabcf45aa3b1f9a4b7978279f8792590b45a37eed435ce57b7d72a0450a`

Hash-verified prior interpretation:

This is the finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `60f50c00298e91552c0f3ee54936e00ab9f2e0f8fa49f646dc9b041ae3179598`

Hash-verified prior interpretation:

This projects heterogeneous exponentiation from the applicable HPow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `6ecc3081362c8634c4eb699026fb8296519b916facae91a3517af0ba69876c50`

Hash-verified prior interpretation:

A matrix with row type m, column type n, and entries α is represented as a function m → n → α.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

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
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `e13788490a4ddd6ff4b4b149324f60ecb8e7a0c0ba610b843d8bfe723b75081e`

Hash-verified prior interpretation:

This gives elements of a monoid their standard natural-number powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `60b25ca730b3f044345386af6b5c4cd605be284726e8529d8750294794ee5501`

Hash-verified prior interpretation:

This interprets a natural-number literal in a type with the corresponding OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `a32c03321ce860001cd2c4902a7abf115c40a20363f82e9b3abf692dc48a9dbc`

Hash-verified prior interpretation:

This supplies the usual real zero and commutative addition as an additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `887b455028b0c64705213f67d7309a4c1e14d10690c1ec3a36f5a6808151c33d`

Hash-verified prior interpretation:

This supplies ordinary real multiplication, one, and natural powers as a monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `5214108629a6d07812769d7a896c21f2e077cef9b79d32f6fedcd9e9723e66b2`

Hash-verified prior interpretation:

This is the nonnegative real square-root function, implemented through the nonnegative-real square root.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `dbb79fafbbcd409e51876cd7225091df1a0b6e0da3463e224a6374329da57fbf`

Hash-verified prior interpretation:

This converts a Pow instance into the corresponding HPow instance with the same result type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `2246ab7a7b13850a8d38ca05ad78918942345dbbe75b4186e5bf96f438540ffa`

Hash-verified prior interpretation:

This interprets every natural-number literal n as that same value in Nat.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Semantic SHA-256: `8eecda35a630fe4097c6149154c07645e87eaf089a78dde5ca01f180806c2a40`
- Reuse SHA-256: `c00b8f579f00c79ba5629157e41bb0b51bbf4202aad0bac21f9eac2abfd9b8ca`

Hash-verified prior interpretation:

This defines matrix multiplication by setting entry (i,k) to the finite dot product Σ_j M(i,j)N(j,k).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
