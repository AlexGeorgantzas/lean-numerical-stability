# Declaration dossier for P10-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t3_recursive_sylvester_error_unroll {n depth : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ)
    (hsep : 0 < sep) (err : ℕ → ℝ)
    (hstep : ∀ k, k < depth →
      err (k + 1) ≤
        p10SylvesterGrowth A B sep * err k +
          p10SylvesterForcing A B C R sep epsilon mu) :
    err depth ≤
      (p10SylvesterGrowth A B sep) ^ depth * err 0 +
        p10SylvesterForcing A B C R sep epsilon mu *
          (∑ k ∈ Finset.range depth, (p10SylvesterGrowth A B sep) ^ k)
```

## Elaborated target type

```lean
∀ {n depth : Nat} (A B C R : HighamBench.P10Matrix n) (sep epsilon mu : Real),
  Real.instLT.lt 0 sep →
    ∀ (err : Nat → Real),
      (∀ (k : Nat),
          instLTNat.lt k depth →
            Real.instLE.le (err (instHAdd.hAdd k 1))
              (instHAdd.hAdd (instHMul.hMul (HighamBench.p10SylvesterGrowth A B sep) (err k))
                (HighamBench.p10SylvesterForcing A B C R sep epsilon mu))) →
        Real.instLE.le (err depth)
          (instHAdd.hAdd (instHMul.hMul (instHPow.hPow (HighamBench.p10SylvesterGrowth A B sep) depth) (err 0))
            (instHMul.hMul (HighamBench.p10SylvesterForcing A B C R sep epsilon mu)
              ((Finset.range depth).sum fun k => instHPow.hPow (HighamBench.p10SylvesterGrowth A B sep) k)))
```

## Fully explicit elaborated target type

```lean
∀ {n depth : Nat} (A B C R : HighamBench.P10Matrix n) (sep epsilon mu : Real)
  (hsep : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) sep)
  (err : Nat → Real)
  (hstep :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k depth →
        @LE.le.{0} Real Real.instLE
          (err
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HighamBench.p10SylvesterGrowth n A B sep) (err k))
            (@HighamBench.p10SylvesterForcing n A B C R sep epsilon mu))),
  @LE.le.{0} Real Real.instLE (err depth)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (@HighamBench.p10SylvesterGrowth n A B sep) depth)
        (err (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HighamBench.p10SylvesterForcing n A B C R sep epsilon mu)
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (Finset.range depth) fun (k : Nat) =>
          @HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HighamBench.p10SylvesterGrowth n A B sep) k)))
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

### D002: `HighamBench.p10SylvesterForcing`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2330216b09375714eafda759f25cab089094fa5c3aee9a52c6089f011132bc46`

Type:

```lean
{n : Nat} →
  HighamBench.P10Matrix n →
    HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n → Real → Real → Real → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B C R : HighamBench.P10Matrix n) → (sep epsilon mu : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B C R sep epsilon mu =>
  instHMul.hMul (instHDiv.hDiv epsilon sep)
    (instHAdd.hAdd (instHMul.hMul 3 (HighamBench.p10FrobNorm C))
      (instHMul.hMul
        (instHMul.hMul (instHMul.hMul 2 mu) (instHAdd.hAdd (HighamBench.p10FrobNorm A) (HighamBench.p10FrobNorm B)))
        (HighamBench.p10FrobNorm R)))
```

### D003: `HighamBench.p10SylvesterGrowth`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f7b32925d56eb327aee4e335bad523200f03a7e4381ee87511381f7be62c3822`

Type:

```lean
{n : Nat} → HighamBench.P10Matrix n → HighamBench.P10Matrix n → Real → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : HighamBench.P10Matrix n) → (sep : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B sep =>
  instHAdd.hAdd 4
    (instHDiv.hDiv (instHMul.hMul 2 (instHAdd.hAdd (HighamBench.p10FrobNorm A) (HighamBench.p10FrobNorm B))) sep)
```

### D004: `HighamBench.p10FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `218361ae17724218614c78ea7e60ed59909b1d6fafeab7842a25909187cad311`
- Reuse SHA-256: `f0913e4a3cb61ed7354bd6a8d663bbd8b2c93ae29427d84803fab115a0397e5f`

Hash-verified prior interpretation:

This maps a real matrix to the square root of the sum of the squares of all its entries, so it is the unsquared Frobenius norm.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `HighamBench.p10SylvesterForcing._proof_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `c2128dca62968615e359a6325c7f1616277ba7b25371bfb81b5d200ad4169f10`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D006: `HighamBench.p10SylvesterGrowth._proof_1`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `cf84cab1ce903e624601ece5316ee2528afd6cf1b755e7954d9ca7611a53f9e5`

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

### D007: `HighamBench.p10SylvesterGrowth._proof_2`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `b67429a01e375c9b3726bce26639b2ea8b2f6da939ade8cab4f6be469b7fd880`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D008: `Finset.range`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Range`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0d8947d3b91a57604f7b7be615f2ff236f2058a47281af31ea2498635666e9e7`

Type:

```lean
Nat → Finset Nat
```

Fully explicit type:

```lean
(n : Nat) → Finset.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
fun n => { val := Multiset.range n, nodup := ⋯ }
```

### D009: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `de6d317f3a880f3f1114792c82569d34742d40bae7422a3e5db0b5805b28d019`

Hash-verified prior interpretation:

This forms the additive sum of a function over a finite set.

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
- Reuse SHA-256: `26ec858b7914040b62e41dac07549d0e710576ebffcab48ae340f110ef32e4ad`

Hash-verified prior interpretation:

This projects the heterogeneous multiplication operation from the applicable HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `60f50c00298e91552c0f3ee54936e00ab9f2e0f8fa49f646dc9b041ae3179598`

Hash-verified prior interpretation:

This projects heterogeneous exponentiation from the applicable HPow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `30a6ffc7f69a075cd10e87a2d586237b1dc7098e4c686f0874110b84179c4b55`

Hash-verified prior interpretation:

This projects the binary non-strict order relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `LT.lt`

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

### D015: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `e13788490a4ddd6ff4b4b149324f60ecb8e7a0c0ba610b843d8bfe723b75081e`

Hash-verified prior interpretation:

This gives elements of a monoid their standard natural-number powers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `519df6688320448028db3a6368518c22853de54ad47b45d39946022a1e1bdf87`

Hash-verified prior interpretation:

This is the inductive type of natural numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `60b25ca730b3f044345386af6b5c4cd605be284726e8529d8750294794ee5501`

Hash-verified prior interpretation:

This interprets a natural-number literal in a type with the corresponding OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `901954785acc1690e69168c413434be73549452178ff230777d608e0a5c1c72a`

Hash-verified prior interpretation:

This is the mathematical real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instAdd`

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

### D020: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `a32c03321ce860001cd2c4902a7abf115c40a20363f82e9b3abf692dc48a9dbc`

Hash-verified prior interpretation:

This supplies the usual real zero and commutative addition as an additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `1a7b1542350a021093ae24fdcaf462b9362f6c48f6f02fff171623ea4471b7c1`

Hash-verified prior interpretation:

This equips Real with its usual non-strict order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instLT`

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

### D023: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `887b455028b0c64705213f67d7309a4c1e14d10690c1ec3a36f5a6808151c33d`

Hash-verified prior interpretation:

This supplies ordinary real multiplication, one, and natural powers as a monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `7ee4e8807313f6dcf59b99b52940f5cd8eb868799c0b55b8b7ce1b1745581ea7`

Hash-verified prior interpretation:

This equips Real with ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Real.instZero`

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

### D026: `Zero.toOfNat0`

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

### D027: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D028: `instHAdd`

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

### D029: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `e59d6740ce08cc0daa448ab94b648895253d68ac0e9c1eddcd501b2207170f14`

Hash-verified prior interpretation:

This converts a homogeneous Mul instance into the corresponding homogeneous HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `dbb79fafbbcd409e51876cd7225091df1a0b6e0da3463e224a6374329da57fbf`

Hash-verified prior interpretation:

This converts a Pow instance into the corresponding HPow instance with the same result type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `instLTNat`

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

### D032: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `2246ab7a7b13850a8d38ca05ad78918942345dbbe75b4186e5bf96f438540ffa`

Hash-verified prior interpretation:

This interprets every natural-number literal n as that same value in Nat.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `DivInvMonoid.toDiv`

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

### D034: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `cf0e0c079b128caed6b4d65311a6841c6e5632ce09e2aa0f9fb215fea4607413`

Hash-verified prior interpretation:

Fin n is the finite index type whose values correspond to the integers from zero through n minus one.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `HDiv.hDiv`

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

### D036: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `6ecc3081362c8634c4eb699026fb8296519b916facae91a3517af0ba69876c50`

Hash-verified prior interpretation:

A matrix with row type m, column type n, and entries α is represented as a function m → n → α.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instDivInvMonoid`

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

### D038: `Real.instNatCast`

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

### D039: `instHDiv`

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

### D040: `instOfNatAtLeastTwo`

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

### D041: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `a3999a1876b4d406154453fec4f9ac4d68c8269ece8a353478f85850c47b023c`

Hash-verified prior interpretation:

This supplies a finite enumeration of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D042: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `5d4d7dabcf45aa3b1f9a4b7978279f8792590b45a37eed435ce57b7d72a0450a`

Hash-verified prior interpretation:

This is the finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D043: `Nat.AtLeastTwo`

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

### D044: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `5214108629a6d07812769d7a896c21f2e077cef9b79d32f6fedcd9e9723e66b2`

Hash-verified prior interpretation:

This is the nonnegative real square-root function, implemented through the nonnegative-real square root.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
