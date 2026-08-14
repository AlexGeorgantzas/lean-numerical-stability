# Declaration dossier for P06-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p06_t3_householder_product_first_order_expansion
    {m : ℕ} (t : ℝ)
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ∀ r i,
      p06PerturbedState t P E b r i =
        p06ExactState P b r i +
          t * p06FirstOrderState P E b r i +
          t ^ 2 * p06HigherOrderState t P E b r i
```

## Elaborated target type

```lean
∀ {m : Nat} (t : Real) (P E : Nat → Fin m → Fin m → Real) (b : Fin m → Real) (r : Nat) (i : Fin m),
  Eq (HighamBench.p06PerturbedState t P E b r i)
    (instHAdd.hAdd
      (instHAdd.hAdd (HighamBench.p06ExactState P b r i) (instHMul.hMul t (HighamBench.p06FirstOrderState P E b r i)))
      (instHMul.hMul (instHPow.hPow t 2) (HighamBench.p06HigherOrderState t P E b r i)))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} (t : Real) (P E : Nat → Fin m → Fin m → Real) (b : Fin m → Real) (r : Nat) (i : Fin m),
  @Eq.{1} Real (@HighamBench.p06PerturbedState m t P E b r i)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p06ExactState m P b r i)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t
          (@HighamBench.p06FirstOrderState m P E b r i)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) t
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HighamBench.p06HigherOrderState m t P E b r i)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P06Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P06Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p06ExactState`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `19e0a1b4e893ca87a8a8f6ba2c96dc9bf1ee6ad4318a81cb77bd992eeb365792`

Type:

```lean
{m : Nat} → (Nat → Fin m → Fin m → Real) → (Fin m → Real) → Nat → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (P : Nat → Fin m → Fin m → Real) → (b : Fin m → Real) → Nat → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} P b x =>
  Nat.brecOn (motive := fun x => Fin m → Real) x fun x f =>
    HighamBench.p06ExactState.match_1 (fun x => Nat.below (motive := fun x => Fin m → Real) x → Fin m → Real) x
      (fun _ x => b) (fun r x => HighamBench.p06MatVec (P r) x.1) f
```

### D002: `HighamBench.p06FirstOrderState`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b9abfdfae1b4f50cae8994a500fccec3ccf23eee4166ce5357082ab0f6f89321`

Type:

```lean
{m : Nat} → (Nat → Fin m → Fin m → Real) → (Nat → Fin m → Fin m → Real) → (Fin m → Real) → Nat → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (P E : Nat → Fin m → Fin m → Real) → (b : Fin m → Real) → Nat → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} P E b x =>
  Nat.brecOn (motive := fun x => Fin m → Real) x fun x f =>
    HighamBench.p06ExactState.match_1 (fun x => Nat.below (motive := fun x => Fin m → Real) x → Fin m → Real) x
      (fun _ x x_1 => 0)
      (fun r x i =>
        instHAdd.hAdd (HighamBench.p06MatVec (P r) x.1 i)
          (HighamBench.p06MatVec (E r) (HighamBench.p06ExactState P b r) i))
      f
```

### D003: `HighamBench.p06HigherOrderState`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2a3daa6b02507060efb00a673fc9cbb5060481a2258fcbd852e5f4edfa3909e6`

Type:

```lean
{m : Nat} → Real → (Nat → Fin m → Fin m → Real) → (Nat → Fin m → Fin m → Real) → (Fin m → Real) → Nat → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (t : Real) → (P E : Nat → Fin m → Fin m → Real) → (b : Fin m → Real) → Nat → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} t P E b x =>
  Nat.brecOn (motive := fun x => Fin m → Real) x fun x f =>
    HighamBench.p06ExactState.match_1 (fun x => Nat.below (motive := fun x => Fin m → Real) x → Fin m → Real) x
      (fun _ x x_1 => 0)
      (fun r x i =>
        instHAdd.hAdd
          (instHAdd.hAdd (HighamBench.p06MatVec (P r) x.1 i)
            (HighamBench.p06MatVec (E r) (HighamBench.p06FirstOrderState P E b r) i))
          (instHMul.hMul t (HighamBench.p06MatVec (E r) x.1 i)))
      f
```

### D004: `HighamBench.p06PerturbedState`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `94359818458953e7afa3f69a1adf4ddfb4efb28945de8a4ffc0a3de17791f84d`

Type:

```lean
{m : Nat} → Real → (Nat → Fin m → Fin m → Real) → (Nat → Fin m → Fin m → Real) → (Fin m → Real) → Nat → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (t : Real) → (P E : Nat → Fin m → Fin m → Real) → (b : Fin m → Real) → Nat → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} t P E b x =>
  Nat.brecOn (motive := fun x => Fin m → Real) x fun x f =>
    HighamBench.p06ExactState.match_1 (fun x => Nat.below (motive := fun x => Fin m → Real) x → Fin m → Real) x
      (fun _ x => b)
      (fun r x => HighamBench.p06MatVec (fun i j => instHAdd.hAdd (P r i j) (instHMul.hMul t (E r i j))) x.1) f
```

### D005: `HighamBench.p06ExactState.match_1`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2a8afd8ae783c1643e83ef708007d8e2d8ae790d265dc114c8f36a1bfa3f7242`

Type:

```lean
(motive : Nat → Sort u_1) → (x : Nat) → (Unit → motive 0) → ((r : Nat) → motive r.succ) → motive x
```

Fully explicit type:

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (a : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (r : Nat) → motive (Nat.succ r)) → motive x
```

Definition body (one-level semantic boundary):

```lean
fun motive x h_1 h_2 => Nat.casesOn x (h_1 Unit.unit) fun n => h_2 n
```

### D006: `HighamBench.p06MatVec`

- Role: `local`
- Owner module: `HighamBench.P06Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `893dee110847631319ce412fdc634324446f2cfd73af2c3a356c467875edecc9`

Type:

```lean
{m n : Nat} → (Fin m → Fin n → Real) → (Fin n → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m n : Nat} → (A : Fin m → Fin n → Real) → (x : Fin n → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D007: `Eq`

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

### D008: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `35cd80f32538eefcda539b03768e7c00f9b586a51f411b3a359db43c6306d84f`

Hash-verified prior interpretation:

Fin n is the finite index type containing the natural indices strictly below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HAdd.hAdd`

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

### D010: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `89fc60edf60ba6d6918ccbe1477028840be5ff337bffc59e4094370d4c7a2d4c`

Hash-verified prior interpretation:

Typeclass-dispatched heterogeneous multiplication, resolved here to multiplication of two real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `88820f7cae6a63241206b801489fe4de932578fc8fdb005bb1a1298e80e4bb86`

Hash-verified prior interpretation:

Typeclass-dispatched exponentiation, resolved here to a real base raised to a natural exponent.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `daec3e91ac4f8e1b17579982947d0889a6c78f791b1c9c25611288290c518fc5`

Hash-verified prior interpretation:

Natural-number exponentiation generated from repeated monoid multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `bb6de39b36fb552c9bb735216f6f2c17371e859fdfe96fe8e17efedd8a3e74c6`

Hash-verified prior interpretation:

The type of natural numbers, including zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `7613166a345fae60fef4f1c7c05f7c4516055a5cb3dab5eeaba50d53897b3a28`

Hash-verified prior interpretation:

It interprets a natural-number literal in a type having the corresponding OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `303ff6b2e2cc582b2fd4807105ed1ea5927472ede732288f0f6e4355d5c716c5`

Hash-verified prior interpretation:

The mathematical real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instAdd`

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

### D017: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `e49003ae173d90d31c775774a45f8a38855451cdb3b74a57a20bc9c0777e4e4c`

Hash-verified prior interpretation:

The multiplicative monoid structure of the real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `73165ab722e2dbdfe079cd476631b9f2b118e1ce275a5fc162026a3b2bac9c66`

Hash-verified prior interpretation:

The standard multiplication operation on real numbers.

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
- Reuse SHA-256: `f8d0cc5238c68171194986bbd5d85f6146d591fdb49a548ed67d403668a74eb4`

Hash-verified prior interpretation:

It turns homogeneous multiplication on a type into homogeneous HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `7b1301aa4e00af607d8215a8e8d43300ff702d5b1314f8cde0d466dc9cbb1866`

Hash-verified prior interpretation:

It lifts a Pow operation into homogeneous HPow with the same base and result type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `0cf3859c180af46021ec65c39235b943e7d730151d109d5d26b6ad78830236c1`

Hash-verified prior interpretation:

It interprets a natural numeral as that same natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D024: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → (F_1 : (t : Nat) → (f : @Nat.below.{u} motive t) → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D025: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D026: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `25808dd543547b53eda5905fde9e22c7adce42e2d1c6657e0a7f0506f529a809`

Hash-verified prior interpretation:

The standard additive zero of the real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8544f990089bb705329f8e13de94d6583865877bcb1ebec4f8c096524a17581e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D028: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `f7ed56c9ef26649eb89155e24913e6cbe0af3be9da7a4ef88a2aa203445b918b`

Hash-verified prior interpretation:

It derives the numeral-zero interpretation from a type's Zero instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `fa5e1d6caaf53069776f35167198f6d7a0b6ea37ab50fca3e95d6d81d1aac54a`

Hash-verified prior interpretation:

The finite enumeration instance containing each member of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `f763c9fe1a09e394fa0adc833ed8401d850813d98bbb961aa24b15519e5d5571`

Hash-verified prior interpretation:

Finite summation in an additive commutative monoid, instantiated here as ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `e99c9eddb42f4152aba53e512aa0e1bf7e22f1565b879b8a16831e1e2cb37f59`

Hash-verified prior interpretation:

The finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} →
  (t : Nat) → (zero : motive Nat.zero) → (succ : (n : Nat) → motive (Nat.succ n)) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D033: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `80fdd6fe30816150d44dd01d6942520dc2c307e4df0be4c783d934e8a35ff979`

Hash-verified prior interpretation:

The additive commutative monoid structure of the real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e5d4ec6d7dbc312235968b914130d2d6ec344f051fd5f7c0276905a3c63cc953`

Type:

```lean
Unit
```

Fully explicit type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```
