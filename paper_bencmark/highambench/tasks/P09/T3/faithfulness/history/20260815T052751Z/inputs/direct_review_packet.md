# Declaration dossier for P09-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p09_t3_multidimensional_rms_error_budget
    {m n : ℕ}
    (term : Fin m → Fin n → ℝ) (total : Fin n → ℝ)
    (ε yRms : ℝ) (K remainder : Fin m → ℝ)
    (hdecomp : total = p09VectorSum term)
    (hlocal : ∀ i, p09Rms (term i) ≤ ε * K i * yRms + remainder i) :
    p09Rms total ≤
      ε * (∑ i : Fin m, K i) * yRms + ∑ i : Fin m, remainder i
```

## Elaborated target type

```lean
∀ {m n : Nat} (term : Fin m → Fin n → Real) (total : Fin n → Real) (ε yRms : Real) (K remainder : Fin m → Real),
  Eq total (HighamBench.p09VectorSum term) →
    (∀ (i : Fin m),
        Real.instLE.le (HighamBench.p09Rms (term i))
          (instHAdd.hAdd (instHMul.hMul (instHMul.hMul ε (K i)) yRms) (remainder i))) →
      Real.instLE.le (HighamBench.p09Rms total)
        (instHAdd.hAdd (instHMul.hMul (instHMul.hMul ε (Finset.univ.sum fun i => K i)) yRms)
          (Finset.univ.sum fun i => remainder i))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (term : Fin m → Fin n → Real) (total : Fin n → Real) (ε yRms : Real) (K remainder : Fin m → Real)
  (hdecomp : @Eq.{1} (Fin n → Real) total (@HighamBench.p09VectorSum m n term))
  (hlocal :
    ∀ (i : Fin m),
      @LE.le.{0} Real Real.instLE (@HighamBench.p09Rms n (term i))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε (K i)) yRms)
          (remainder i))),
  @LE.le.{0} Real Real.instLE (@HighamBench.p09Rms n total)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ε
          (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
            fun (i : Fin m) => K i))
        yRms)
      (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
        fun (i : Fin m) => remainder i))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P09Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P09Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p09Rms`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `b4cac0b00ee6a2c54531676b12d6189f6ec59865fd406b873eff812ffbaae2e0`
- Reuse SHA-256: `72c205fc0ddf04451f0901516e2a443d8d9a31fc541ab9054238aa7860abadd6`

Hash-verified prior interpretation:

The definition divides p09VecNorm2 x by sqrt of the real cast of n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D002: `HighamBench.p09VectorSum`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0e1c36cfc0b951764fbcaf33505933b953de6a77d4b57ee30f7e4fb976268d4c`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{m n : Nat} → (term : Fin m → Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} term j => Finset.univ.sum fun i => term i j
```

### D003: `HighamBench.p09VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `e46a30d529d63d20117a9b6fe7731e357b99fbedd664623afde49e38ea68a208`
- Reuse SHA-256: `d29b679e5a807f416243054fc723877481ad14f66c96a9a1891f6394ef48c67e`

Hash-verified prior interpretation:

The definition is the principal real square root of p09VecNorm2Sq x.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p09VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P09Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `1c64a3146c1b228a22c9a0d23d5f84779d43a4d735416607a293c26696b2f483`
- Reuse SHA-256: `718f6c94acd938cf089fd5133847779707008aab4b891b43381a1082f91737c2`

Hash-verified prior interpretation:

The definition sums (x i)^2 over Finset.univ.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `Eq`

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

### D006: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `cd79814e865955529feeef9c171bd40df69b753354e8ddc1c2ff1f6366c9f17e`

Hash-verified prior interpretation:

Fin n is the finite type of natural indices strictly below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `67c1719acafb19f1b140d697ed4656a3d2dd83887ec46571ff88cd7ed6ad38a3`

Hash-verified prior interpretation:

This instance enumerates every element of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `5288ef8106ecb795c3363416fd73460d33935c60506911e876868f2c36768f05`

Hash-verified prior interpretation:

Finset.sum maps the summand over a finite set and adds the results in an additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `28acb81272d20c2cd8ff3732b49f52daa1c40525aad8d36f7b55ea345e62973c`

Hash-verified prior interpretation:

Finset.univ is the finite set containing every element of a Fintype.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `HAdd.hAdd`

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

### D011: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `90f5eb353285dcf746f7822944feee7c2497fbe0e2a622c03ba11b36d0af57a3`

Hash-verified prior interpretation:

This operation projects the heterogeneous multiplication supplied by an HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `66d8fc8aa022f66660f4a24a1b114c84bf44df579a79d815a683f9a47623ca93`

Hash-verified prior interpretation:

This operation projects the non-strict order relation supplied by an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `d7519eafed2c54cc55e07fd66bcdbe97860973add8eec42fc9c9bda67fb5cd87`

Hash-verified prior interpretation:

Nat is the type of nonnegative integers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `71b25a45c25a5a950913a7b2dbf4f8410170fa7c902e552a3fd0380abc0f4467`

Hash-verified prior interpretation:

Real is the exact real-number type used for vector entries, norms, square roots, products, and inequalities.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Real.instAdd`

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

### D016: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `30221d0dbd687d326ed38f104ed0fa7ba456b2ba5be10199815d43c92e52ce3d`

Hash-verified prior interpretation:

This instance supplies real zero and commutative addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `87866b29bc0bab98dff0c087a43cd7459dfe809b0fcf072c7aa1343b4b7e5570`

Hash-verified prior interpretation:

This instance supplies the standard order relation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `39d48a732a2a33f83139bbc6cb85e6fc66d0c5684ec46fc6f615b22cdcde4bbf`

Hash-verified prior interpretation:

This instance supplies ordinary multiplication of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `instHAdd`

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

### D020: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `2442771e163b14ff68ef1c6c0257b7060bb52d0e568fade6d7214a7ed2e23515`

Hash-verified prior interpretation:

This instance lifts a homogeneous Mul operation to HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `76a67940d6613ef7969675aa3d226a144bf1139d160483038c80ee5a357dd236`

Hash-verified prior interpretation:

This projection supplies division from the real DivInvMonoid structure.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `b64f8629edb00501ebd84ba62cf9ef9b7437bfda3448a94bcbd97cd7559a8539`

Hash-verified prior interpretation:

This operation projects heterogeneous division from an HDiv instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`
- Reuse SHA-256: `937c28935d916b91029fc66081257a960d934e971654415d0cfbe3c179aacca6`

Hash-verified prior interpretation:

This operation maps a natural number through the selected NatCast instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `ce3be1507c38e8e8aab4532c83e37e1306c6e99ee071b19865e356b9828042aa`

Hash-verified prior interpretation:

This instance supplies ordinary real inversion and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`
- Reuse SHA-256: `241de7bc337bcfbc9e6893272d04cb2fef013e204b77c81090e61d0c153551da`

Hash-verified prior interpretation:

This instance embeds natural numbers canonically into the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `e269785d16bc98a2df37cfe84cf49d662f8eefb644892aa7511d6b9997736ecd`

Hash-verified prior interpretation:

Real.sqrt is the nonnegative principal square root on reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `c8336ab7caf16b5ed3fe6c7da7a3ba7e02410e11bc0223c048646d06775756cb`

Hash-verified prior interpretation:

This instance lifts a homogeneous Div operation to HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `84bd0ac8320aeef45754d420074f5c42d59e1075dcab88407d17cc3c71f3a862`

Hash-verified prior interpretation:

This operation projects heterogeneous exponentiation from an HPow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `218460eb742e368d57358aa321233404b48243177028b181e528fa71d6690f52`

Hash-verified prior interpretation:

This instance defines natural powers by repeated monoid multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `ac2073e314c31df0d66cc11bc463c1a740e8aa6cca22c4bfb210da1f5a6190b2`

Hash-verified prior interpretation:

This operation interprets a numeral through an OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `5435298d44bb1656378a4f37e919e8c82091e6a069d59cf5055f96c91f7716a0`

Hash-verified prior interpretation:

This instance supplies real one and multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `e631454bb089cf5a979f267aa7525d2f848a888d0e2ff32dd74cdb1cceda2aac`

Hash-verified prior interpretation:

This instance lifts a Pow operation to HPow.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `17ecac36244e6f1109e5f13d5088144ea8eb6f8e5a49fa472d12f29340ba6d40`

Hash-verified prior interpretation:

This instance interprets each natural numeral as itself.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
