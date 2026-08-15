# Declaration dossier for P09-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p09_t2_scaled_orthogonal_backward_error
    {n : ℕ} (Q : Fin n → Fin n → ℝ) (e : Fin n → ℝ) (s : ℝ)
    (hs : 0 < s) (hQ : p09Orthogonal Q) :
    ∃ δ : Fin n → ℝ,
      p09MatVec (p09ScaleMatrix s Q) δ = e ∧
      p09VecNorm2 δ = p09VecNorm2 e / s ∧
      p09Max δ ≤ p09VecNorm2 δ
```

## Elaborated target type

```lean
∀ {n : Nat} (Q : Fin n → Fin n → Real) (e : Fin n → Real) (s : Real),
  Real.instLT.lt 0 s →
    HighamBench.p09Orthogonal Q →
      Exists fun δ =>
        And (Eq (HighamBench.p09MatVec (HighamBench.p09ScaleMatrix s Q) δ) e)
          (And (Eq (HighamBench.p09VecNorm2 δ) (instHDiv.hDiv (HighamBench.p09VecNorm2 e) s))
            (Real.instLE.le (HighamBench.p09Max δ) (HighamBench.p09VecNorm2 δ)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (Q : Fin n → Fin n → Real) (e : Fin n → Real) (s : Real)
  (hs : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) s)
  (hQ : @HighamBench.p09Orthogonal n Q),
  @Exists.{1} (Fin n → Real) fun (δ : Fin n → Real) =>
    And (@Eq.{1} (Fin n → Real) (@HighamBench.p09MatVec n (@HighamBench.p09ScaleMatrix n s Q) δ) e)
      (And
        (@Eq.{1} Real (@HighamBench.p09VecNorm2 n δ)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HighamBench.p09VecNorm2 n e) s))
        (@LE.le.{0} Real Real.instLE (@HighamBench.p09Max n δ) (@HighamBench.p09VecNorm2 n δ)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P09Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P09Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p09MatVec`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `01ba80b1cc7323772b5743139f62c26b516f7c8086a59c99a00be77e45f1c29b`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D002: `HighamBench.p09Max`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `24619388a7774ee6c58f7db15c1d4dfb8beb8b217a8cff261115552769f8a822`
- Reuse SHA-256: `c8512222d160e22c723abaf62d95ecd9173bef56e3be16784475ea187ef23426`

Hash-verified prior interpretation:

The definition is the norm of a finite real-valued function under the Pi normed-ring instance; for nonempty Fin n this is the supremum, hence the maximum, of the component absolute values.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D003: `HighamBench.p09Orthogonal`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e9af45aca7c9f15c50eabb53d3a6e34212a61a85dff588e4d4070c1ab0490e4a`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (Q : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} Q =>
  And (HighamBench.p09IsLeftInverse Q (HighamBench.p09Transpose Q))
    (HighamBench.p09IsRightInverse Q (HighamBench.p09Transpose Q))
```

### D004: `HighamBench.p09ScaleMatrix`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe3241ab0430e624ff8e32bcd9a0a515aab4973d3394ec203b3dfef1f352c20c`

Type:

```lean
{n : Nat} → Real → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (s : Real) → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} s A i j => instHMul.hMul s (A i j)
```

### D005: `HighamBench.p09VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `e46a30d529d63d20117a9b6fe7731e357b99fbedd664623afde49e38ea68a208`
- Reuse SHA-256: `d29b679e5a807f416243054fc723877481ad14f66c96a9a1891f6394ef48c67e`

Hash-verified prior interpretation:

The definition is the principal real square root of p09VecNorm2Sq x.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HighamBench.p09IsLeftInverse`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `ee72eed87339eea13325e636c6887069b9ce7ea95c4cdf3a0fd871b9a5f50fae`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => ∀ (i j : Fin n), Eq (Finset.univ.sum fun k => instHMul.hMul (Ainv i k) (A k j)) (ite (Eq i j) 1 0)
```

### D007: `HighamBench.p09IsRightInverse`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `36226956ab2a82dc74ff26152b2e72aa5743fd9788b7b30739d2dabbcfd719fa`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => ∀ (i j : Fin n), Eq (Finset.univ.sum fun k => instHMul.hMul (A i k) (Ainv k j)) (ite (Eq i j) 1 0)
```

### D008: `HighamBench.p09Transpose`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `acc4fdc1b6b9d6f1131b203aeb131a0bd79fab88dd6063bfbc52fe99ae247fe0`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A i j => A j i
```

### D009: `HighamBench.p09VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `1c64a3146c1b228a22c9a0d23d5f84779d43a4d735416607a293c26696b2f483`
- Reuse SHA-256: `718f6c94acd938cf089fd5133847779707008aab4b891b43381a1082f91737c2`

Hash-verified prior interpretation:

The definition sums (x i)^2 over Finset.univ.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `And`

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

### D011: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `76a67940d6613ef7969675aa3d226a144bf1139d160483038c80ee5a357dd236`

Hash-verified prior interpretation:

This projection supplies division from the real DivInvMonoid structure.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Eq`

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

### D013: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D014: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `cd79814e865955529feeef9c171bd40df69b753354e8ddc1c2ff1f6366c9f17e`

Hash-verified prior interpretation:

Fin n is the finite type of natural indices strictly below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `b64f8629edb00501ebd84ba62cf9ef9b7437bfda3448a94bcbd97cd7559a8539`

Hash-verified prior interpretation:

This operation projects heterogeneous division from an HDiv instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `66d8fc8aa022f66660f4a24a1b114c84bf44df579a79d815a683f9a47623ca93`

Hash-verified prior interpretation:

This operation projects the non-strict order relation supplied by an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`
- Reuse SHA-256: `40c66835aee13b8def7fe72c7b12efdb478625f8ffbdd4d2c9e41fb39d0e8f14`

Hash-verified prior interpretation:

This operation projects the strict order relation supplied by an LT instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `d7519eafed2c54cc55e07fd66bcdbe97860973add8eec42fc9c9bda67fb5cd87`

Hash-verified prior interpretation:

Nat is the type of nonnegative integers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `ac2073e314c31df0d66cc11bc463c1a740e8aa6cca22c4bfb210da1f5a6190b2`

Hash-verified prior interpretation:

This operation interprets a numeral through an OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `71b25a45c25a5a950913a7b2dbf4f8410170fa7c902e552a3fd0380abc0f4467`

Hash-verified prior interpretation:

Real is the exact real-number type used for vector entries, norms, square roots, products, and inequalities.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `ce3be1507c38e8e8aab4532c83e37e1306c6e99ee071b19865e356b9828042aa`

Hash-verified prior interpretation:

This instance supplies ordinary real inversion and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `87866b29bc0bab98dff0c087a43cd7459dfe809b0fcf072c7aa1343b4b7e5570`

Hash-verified prior interpretation:

This instance supplies the standard order relation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D024: `Real.instZero`

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

### D025: `Zero.toOfNat0`

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

### D026: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `c8336ab7caf16b5ed3fe6c7da7a3ba7e02410e11bc0223c048646d06775756cb`

Hash-verified prior interpretation:

This instance lifts a homogeneous Div operation to HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `67c1719acafb19f1b140d697ed4656a3d2dd83887ec46571ff88cd7ed6ad38a3`

Hash-verified prior interpretation:

This instance enumerates every element of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `5288ef8106ecb795c3363416fd73460d33935c60506911e876868f2c36768f05`

Hash-verified prior interpretation:

Finset.sum maps the summand over a finite set and adds the results in an additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `28acb81272d20c2cd8ff3732b49f52daa1c40525aad8d36f7b55ea345e62973c`

Hash-verified prior interpretation:

Finset.univ is the finite set containing every element of a Fintype.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `90f5eb353285dcf746f7822944feee7c2497fbe0e2a622c03ba11b36d0af57a3`

Hash-verified prior interpretation:

This operation projects the heterogeneous multiplication supplied by an HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`
- Reuse SHA-256: `24d7edfd6b2fb01434919c04a868fd4f8da656c431c05f635ac219828fe6a566`

Hash-verified prior interpretation:

This operation projects the norm function from a Norm instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `NormedCommRing.toNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `ff5852fa6ac00f6a258a1d8fe950a0ed74f219c79c926896eb081436331a480e`
- Reuse SHA-256: `36379818a343cb840725693a05cf58bde265ca384f317dd0e6388c35cc8940ed`

Hash-verified prior interpretation:

This projection obtains a NormedRing structure from a NormedCommRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`
- Reuse SHA-256: `3d13f77b716fd5f6fbf2840d67d536a8433c7477fbea6da05448396fd0543f8d`

Hash-verified prior interpretation:

This projection extracts a Norm operation from a NormedRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Pi.normedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Lemmas`
- Declaration kind: `def`
- Semantic SHA-256: `f9dab15f307cbf227004c74c0bb06dec60fd13239b8d79b0751df5ec0ca2a0d9`
- Reuse SHA-256: `a0f125a7c1305c382cbaf983ccb4c152a1aed947f0f3c2a5569786d2f07adfa5`

Hash-verified prior interpretation:

For a finitely indexed family of normed rings, this constructs the pointwise function normed ring with norm equal to the finite supremum of component norms.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `30221d0dbd687d326ed38f104ed0fa7ba456b2ba5be10199815d43c92e52ce3d`

Hash-verified prior interpretation:

This instance supplies real zero and commutative addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `39d48a732a2a33f83139bbc6cb85e6fc66d0c5684ec46fc6f615b22cdcde4bbf`

Hash-verified prior interpretation:

This instance supplies ordinary multiplication of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.normedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `69cccc1e864661e103785f4a2712b9ad164d845c03b7737801c37e5ac852bad7`
- Reuse SHA-256: `3890559802d212ef968f94bde4782df49c4b8a7539b35fa572d3003cd855c322`

Hash-verified prior interpretation:

This is the standard normed commutative-ring structure on the reals, with ordinary arithmetic and absolute-value norm.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `e269785d16bc98a2df37cfe84cf49d662f8eefb644892aa7511d6b9997736ecd`

Hash-verified prior interpretation:

Real.sqrt is the nonnegative principal square root on reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `2442771e163b14ff68ef1c6c0257b7060bb52d0e568fade6d7214a7ed2e23515`

Hash-verified prior interpretation:

This instance lifts a homogeneous Mul operation to HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `84bd0ac8320aeef45754d420074f5c42d59e1075dcab88407d17cc3c71f3a862`

Hash-verified prior interpretation:

This operation projects heterogeneous exponentiation from an HPow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D041: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `218460eb742e368d57358aa321233404b48243177028b181e528fa71d6690f52`

Hash-verified prior interpretation:

This instance defines natural powers by repeated monoid multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D042: `One.toOfNat1`

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

### D043: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `5435298d44bb1656378a4f37e919e8c82091e6a069d59cf5055f96c91f7716a0`

Hash-verified prior interpretation:

This instance supplies real one and multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D044: `Real.instOne`

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

### D045: `instDecidableEqFin`

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

### D046: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `e631454bb089cf5a979f267aa7525d2f848a888d0e2ff32dd74cdb1cceda2aac`

Hash-verified prior interpretation:

This instance lifts a Pow operation to HPow.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D047: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `17ecac36244e6f1109e5f13d5088144ea8eb6f8e5a49fa472d12f29340ba6d40`

Hash-verified prior interpretation:

This instance interprets each natural numeral as itself.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D048: `ite`

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
