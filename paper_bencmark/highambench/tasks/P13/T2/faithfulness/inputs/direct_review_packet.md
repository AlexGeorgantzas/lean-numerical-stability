# Declaration dossier for P13-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p13_t2_data_perturbation_bound {n : ℕ}
    (ell f deltaF : Fin n → ℝ) (epsilon : ℝ)
    (hdelta : ∀ i, |deltaF i| ≤ epsilon * |f i|)
    (hvalue : p13InterpolationValue ell f ≠ 0) :
    |p13InterpolationValue ell (fun i => f i + deltaF i) -
        p13InterpolationValue ell f| /
        |p13InterpolationValue ell f| ≤
      epsilon * p13Condition ell f
```

## Elaborated target type

```lean
∀ {n : Nat} (ell f deltaF : Fin n → Real) (epsilon : Real),
  (∀ (i : Fin n), Real.instLE.le (abs (deltaF i)) (instHMul.hMul epsilon (abs (f i)))) →
    Ne (HighamBench.p13InterpolationValue ell f) 0 →
      Real.instLE.le
        (instHDiv.hDiv
          (abs
            (instHSub.hSub (HighamBench.p13InterpolationValue ell fun i => instHAdd.hAdd (f i) (deltaF i))
              (HighamBench.p13InterpolationValue ell f)))
          (abs (HighamBench.p13InterpolationValue ell f)))
        (instHMul.hMul epsilon (HighamBench.p13Condition ell f))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (ell f deltaF : Fin n → Real) (epsilon : Real)
  (hdelta :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (deltaF i))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
          (@abs.{0} Real Real.lattice Real.instAddGroup (f i))))
  (hvalue :
    @Ne.{1} Real (@HighamBench.p13InterpolationValue n ell f)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HighamBench.p13InterpolationValue n ell fun (i : Fin n) =>
            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (f i) (deltaF i))
          (@HighamBench.p13InterpolationValue n ell f)))
      (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p13InterpolationValue n ell f)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon (@HighamBench.p13Condition n ell f))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P13Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P13Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p13Condition`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d7fa6d0b4989adc94f4aad1f81cfa4b3701ddea99c39dd03e0dff65ff72bb46d`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (ell f : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ell f =>
  instHDiv.hDiv (Finset.univ.sum fun i => abs (instHMul.hMul (ell i) (f i)))
    (abs (HighamBench.p13InterpolationValue ell f))
```

### D002: `HighamBench.p13InterpolationValue`

- Role: `local`
- Owner module: `HighamBench.P13Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `70562d0bc0d8c2ac0f383af2d951ff600b8a30ab3a85c099f9d4f449c22ebc0b`
- Reuse SHA-256: `91651a431909eb18900aed94b174f42faeaf9eb340bc7bda4e2d4e78c2f2070c`

Hash-verified prior interpretation:

This is the exact real finite sum of the products ell i * f i.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D003: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `7d038def03b8b04afde21f875edb707b3ff548ef11d2da4fa55b6043d015b1e0`

Hash-verified prior interpretation:

This extracts division from a division-and-inverse monoid structure.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `Fin`

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

### D006: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `95bbeabfe5a449f2ba09086bbe1d6364b401db913c8278859fe06ad567803d42`

Hash-verified prior interpretation:

This dispatches heterogeneous division through the selected HDiv instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `604a960639af0efce7efa7efc6f134fe051b3c5dc1c48c78ffaa9ce8b9649dcc`

Hash-verified prior interpretation:

This dispatches heterogeneous multiplication through the selected HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D009: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `8fc86d4b46d47573c7084325585f71d53c2195bd6ef436faef4ed7aa61e99ee1`

Hash-verified prior interpretation:

This projects the binary non-strict order relation supplied by the relevant LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `Nat`

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

### D011: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`
- Reuse SHA-256: `b379281ac30d72322e40b97d7100066d7c3c750cf0a953ab0d40f3f1f1d1ec74`

Hash-verified prior interpretation:

Ne a b means not (a = b).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `217c6c364afad38f28c563d138bedd706cd225dea80409f4bcf8f9a16838ef56`

Hash-verified prior interpretation:

This obtains a typed numeral from the corresponding OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `a8b1d6c8a236c9000a59f2eddfc4bb9eafa545405b21f06782cfbb22d6531335`

Hash-verified prior interpretation:

Real is Lean's type of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Real.instAdd`

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

### D015: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `f2e72b4b339dff0a5dbbcbc0ccd3af8d122f0604199b14886775db5e57dc5221`

Hash-verified prior interpretation:

This supplies real addition, zero, and additive inverses.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `7666c0953a2efc300f90fdd768e88421404d01fba675a21f058f5fc0f8a66dc7`

Hash-verified prior interpretation:

This supplies real multiplication, inversion, and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `ad12fb8bfe185a50548cde2b1fe4430aad1d1eb5e7fe6cf41615c4a56a579fb8`

Hash-verified prior interpretation:

This is the standard non-strict order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `9226216e945c56e1f162c24801f8900aba95bcadd64b323b1fac2328074c418f`

Hash-verified prior interpretation:

This supplies ordinary multiplication on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D020: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `1e61978cbbd3b176de599693b6db2ada4fe690d45638f7c75a3bd4b054dd6004`

Hash-verified prior interpretation:

This supplies the additive identity 0 in the real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `a9ded547c0f64bfdaedff72c03dbb5e290c4f75262960fff2d5fd356320f4732`

Hash-verified prior interpretation:

This supplies the standard lattice order, including maximum and minimum, on the real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `6f4d693d3279d6348a8beabfa01ca7ac2e6db5ec0904d145c0a3d72f15281a3a`

Hash-verified prior interpretation:

This constructs the numeral-zero interpretation from a Zero instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `5600a951864c72f91f5551c89acab72b0c37a8a9e178e5335c0917eca73e1e9a`

Hash-verified prior interpretation:

In this ordered additive group, abs a is max(a,-a), which for real a is the usual nonnegative absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `instHAdd`

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

### D025: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `3b34ef37f7beb75ebd0cda4c2464144e16d11cdad3fa2c07eacd02e6277977fc`

Hash-verified prior interpretation:

This converts a homogeneous Div operation into the corresponding homogeneous HDiv operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `c527b442abb61196db8a735ab550d0c90390f8e2c1b3f3936c52414a4c6c9578`

Hash-verified prior interpretation:

This converts a homogeneous Mul operation into the corresponding homogeneous HMul operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D028: `Fin.fintype`

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

### D029: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `2c83cd50974a10e9bfd9b166e086a82ede265eb6fd123d760d924382ca48b01b`

Hash-verified prior interpretation:

This folds addition over a finite set after applying the supplied summand function.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Finset.univ`

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

### D031: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `61817d1b06dbd530df02033695349dedbd248eef070112791c2f7bb2cebe065a`

Hash-verified prior interpretation:

This supplies associative, commutative real addition with identity zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
