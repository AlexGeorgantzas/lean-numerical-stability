# Declaration dossier for P17-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p17_t3_variance_plus_bias_probability_bound
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    (centered : Ω → ℝ) (bias varianceBudget biasRadius kappa lambda : ℝ)
    (hvariance : 0 < varianceBudget) (hlambda : 0 < lambda)
    (hkappa : 0 ≤ kappa)
    (hmoment : p17Expectation P (fun ω => (centered ω) ^ 2) ≤ varianceBudget)
    (hbias : |bias| ≤ biasRadius) :
    1 - lambda ≤
      p17EventProb P {ω |
        |kappa * (centered ω + bias)| ≤
          kappa * (Real.sqrt (varianceBudget / lambda) + biasRadius)}
```

## Elaborated target type

```lean
∀ {Ω : Type u_1} [inst : Fintype Ω] (P : HighamBench.P17FiniteProbability Ω) (centered : Ω → Real)
  (bias varianceBudget biasRadius kappa lambda : Real),
  Real.instLT.lt 0 varianceBudget →
    Real.instLT.lt 0 lambda →
      Real.instLE.le 0 kappa →
        Real.instLE.le (HighamBench.p17Expectation P fun ω => instHPow.hPow (centered ω) 2) varianceBudget →
          Real.instLE.le (abs bias) biasRadius →
            Real.instLE.le (instHSub.hSub 1 lambda)
              (HighamBench.p17EventProb P
                (setOf fun ω =>
                  Real.instLE.le (abs (instHMul.hMul kappa (instHAdd.hAdd (centered ω) bias)))
                    (instHMul.hMul kappa (instHAdd.hAdd (instHDiv.hDiv varianceBudget lambda).sqrt biasRadius))))
```

## Fully explicit elaborated target type

```lean
∀ {Ω : Type u_1} [inst : Fintype.{u_1} Ω] (P : @HighamBench.P17FiniteProbability.{u_1} Ω inst) (centered : Ω → Real)
  (bias varianceBudget biasRadius kappa lambda : Real)
  (hvariance :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      varianceBudget)
  (hlambda :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lambda)
  (hkappa :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) kappa)
  (hmoment :
    @LE.le.{0} Real Real.instLE
      (@HighamBench.p17Expectation.{u_1} Ω inst P fun (ω : Ω) =>
        @HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (centered ω) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      varianceBudget)
  (hbias : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup bias) biasRadius),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) lambda)
    (@HighamBench.p17EventProb.{u_1} Ω inst P
      (@setOf.{u_1} Ω fun (ω : Ω) =>
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) kappa
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (centered ω) bias)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) kappa
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) varianceBudget lambda))
              biasRadius))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P17Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P17Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P17FiniteProbability`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cdc6900d6b44706c8faf4d7e391274862067cb6d95b1131a47b2560a766d95d3`

Type:

```lean
(Ω : Type u_1) → [Fintype Ω] → Type u_1
```

Fully explicit type:

```lean
(Ω : Type u_1) → [Fintype.{u_1} Ω] → Type u_1
```

### D002: `HighamBench.p17EventProb`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ede349ac6e2be7773e1e3d332fa662acecc14a263f8143eec3791e9e016534b2`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17FiniteProbability Ω → Set Ω → Real
```

Fully explicit type:

```lean
{Ω : Type u_1} →
  [inst : Fintype.{u_1} Ω] → (P : @HighamBench.P17FiniteProbability.{u_1} Ω inst) → (E : Set.{u_1} Ω) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [Fintype Ω] P E => Finset.univ.sum fun ω => ite (Set.instMembership.mem E ω) (P.prob ω) 0
```

### D003: `HighamBench.p17Expectation`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `11fae07829d61b57addb3f2e2be7e9036d8a1f8a8ef1b16838117ee6186916da`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17FiniteProbability Ω → (Ω → Real) → Real
```

Fully explicit type:

```lean
{Ω : Type u_1} → [inst : Fintype.{u_1} Ω] → (P : @HighamBench.P17FiniteProbability.{u_1} Ω inst) → (X : Ω → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {Ω} [Fintype Ω] P X => Finset.univ.sum fun ω => instHMul.hMul (P.prob ω) (X ω)
```

### D004: `HighamBench.P17FiniteProbability.mk`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `fd0a240d1fc266d3cd085bc0f6cc5d37e8496bf562c971bd11b5f95e9e7b4d90`

Type:

```lean
{Ω : Type u_1} →
  [inst : Fintype Ω] →
    (prob : Ω → Real) →
      (∀ (ω : Ω), Real.instLE.le 0 (prob ω)) →
        Eq (Finset.univ.sum fun ω => prob ω) 1 → HighamBench.P17FiniteProbability Ω
```

Fully explicit type:

```lean
{Ω : Type u_1} →
  [inst : Fintype.{u_1} Ω] →
    (prob : Ω → Real) →
      (prob_nonneg :
          ∀ (ω : Ω),
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (prob ω)) →
        (prob_sum :
            @Eq.{1} Real
              (@Finset.sum.{u_1, 0} Ω Real Real.instAddCommMonoid (@Finset.univ.{u_1} Ω inst) fun (ω : Ω) => prob ω)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          @HighamBench.P17FiniteProbability.{u_1} Ω inst
```

### D005: `HighamBench.P17FiniteProbability.prob`

- Role: `local`
- Owner module: `HighamBench.P17Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `3636c9f4d2f36ba03c4caf5f0ddd2ad616a29ee70ad7e10bc918a28de663df17`

Type:

```lean
{Ω : Type u_1} → [inst : Fintype Ω] → HighamBench.P17FiniteProbability Ω → Ω → Real
```

Fully explicit type:

```lean
{Ω : Type u_1} → [inst : Fintype.{u_1} Ω] → (self : @HighamBench.P17FiniteProbability.{u_1} Ω inst) → Ω → Real
```

Definition body (one-level semantic boundary):

```lean
fun Ω [Fintype Ω] self => self.1
```

### D006: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D007: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D008: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `8e238a782a5fa590cf4b1016f83e5f0f68ef2ffa7f08828d92e4751b917d3094`

Hash-verified prior interpretation:

Typeclass-dispatched addition, instantiated here as ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D010: `HMul.hMul`

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

### D011: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `ae427df10665c63a10e9f5d6e8e18ac7b758e79d1f0955f4c3ca097fff66c85d`

Hash-verified prior interpretation:

Typeclass-dispatched exponentiation, instantiated as natural-number powers of reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `acf46554bba0caeba7168c2bd11bf9a41b4510a9dac46d3f3cd39b8a2e858287`

Hash-verified prior interpretation:

Typeclass-dispatched subtraction, instantiated as ordinary real subtraction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `0dcd4d54dc5efe73d79e4b04d175f2dca920b0224dc82b6e16091b7f8d35baaa`

Hash-verified prior interpretation:

The non-strict order relation supplied by the relevant LE instance.

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
- Reuse SHA-256: `fe46aa204372eb5439324019fd0953697fe646c07328127f2604d3111db326ea`

Hash-verified prior interpretation:

Defines x raised to a natural exponent by repeated monoid multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Nat`

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

### D017: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `9412c8799dd7ab5a9cd03a6289b408558cf47f44c8678d5f9fcd39132aa90a1d`

Hash-verified prior interpretation:

Interprets natural-number literals in a target type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`
- Reuse SHA-256: `1c662a114670d76bda6f45c1caef6f56839c8751fcd1c29ba6602c9e4eac9386`

Hash-verified prior interpretation:

Derives interpretation of the numeral 1 from the real multiplicative identity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real`

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

### D020: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `e64b5c91700232551ae1fd439ea5d1ba590397e612faaf16f62a23cc5c378695`

Hash-verified prior interpretation:

Ordinary addition on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `953242ba6ab9ee59ca4aeeae55b66c1f65ae1b3ec736bb896a8082722e08a850`

Hash-verified prior interpretation:

The additive-group structure of the reals, including addition, negation, and zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D023: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `05753e0845504079b2a49760ce0760bba31bd490a1fbbbec350ab090bf5f6150`

Hash-verified prior interpretation:

The usual non-strict linear order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instLT`

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

### D025: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `f4f35dbd3354a3a2c6e30a12525fb25ce21682401bd0b8c6c4a2b89afdaece9f`

Hash-verified prior interpretation:

The multiplicative monoid structure of the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.instMul`

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

### D027: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`
- Reuse SHA-256: `e51a242fc9e06a843daf48323e127b9a5e24e589e9139d1c4d178817cc4f01b4`

Hash-verified prior interpretation:

The real multiplicative identity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `cae5df6a1fe8b8368ddc76512a5e3b97db34cf5aa11faf1cff630d6f5dd7eb35`

Hash-verified prior interpretation:

Real subtraction defined as addition of the additive inverse.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `add1e0d38b718ff561745d67e457a3e5a9e88523d6641af854dd815b11797de6`

Hash-verified prior interpretation:

The real additive identity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `5c94154655daa21d92ca5ad3ae013135ac73fc292c856c799cf18acc88e6c476`

Hash-verified prior interpretation:

The lattice structure induced by the usual order on the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D032: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `4ffc57c777cabc45c64299faad3978aad738b122dda5156a2ea75d97ce8a5347`

Hash-verified prior interpretation:

Derives interpretation of the numeral 0 from the real additive identity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`

Type:

```lean
{α : Type u_1} → [Lattice α] → [AddGroup α] → α → α
```

Fully explicit type:

```lean
{α : Type u_1} → [Lattice.{u_1} α] → [AddGroup.{u_1} α] → (a : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D034: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `634c32b54fc9e5d8e0d6c15053ec736151828bfac08d0e430707a48416bcb433`

Hash-verified prior interpretation:

Lifts homogeneous real addition into the heterogeneous-addition interface.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D036: `instHMul`

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

### D037: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `265c3ec48b8a93626c5d1509c62aa0d0670a6d1f84ee18a4d0a74fe156315b23`

Hash-verified prior interpretation:

Lifts real natural powers into the heterogeneous-power interface.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `9acf234ffe7767f8c9d61a522c93ace13daa9ca28ce1049c951e39128f4bf717`

Hash-verified prior interpretation:

Lifts homogeneous real subtraction into the heterogeneous-subtraction interface.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `instOfNatNat`

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

### D040: `setOf`

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

### D041: `Classical.propDecidable`

- Role: `external-frontier`
- Owner module: `Init.Classical`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `823c02cb7dcdb8ce30edfb12a2496dda0849f0773c65f9e91e289fab27c36c46`

Type:

```lean
(a : Prop) → Decidable a
```

Fully explicit type:

```lean
(a : Prop) → Decidable a
```

Definition body (one-level semantic boundary):

```lean
fun a => Classical.choice ⋯
```

### D042: `Finset.sum`

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

### D043: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `e1c319c6b4ed4d5f6114006b06fd0104d65483830507f476dc0b7a6c1f1fe0be`

Hash-verified prior interpretation:

The finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D044: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `941ea3346e809f919727c21bfcdeea342714a6b83f1cf871d648aa2cb14d6e9e`

Type:

```lean
{α : outParam (Type u)} → {γ : Type v} → [self : Membership α γ] → γ → α → Prop
```

Fully explicit type:

```lean
{α : outParam.{u + 2} (Type u)} → {γ : Type v} → [self : Membership.{u, v} α γ] → γ → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} γ [self : Membership α γ] => self.1
```

### D045: `Real.instAddCommMonoid`

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

### D046: `Set`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a6e551515032966c16e4f42e4548ff1854c2dce05ffe51e98b66943caecc78ec`

Type:

```lean
Type u → Type u
```

Fully explicit type:

```lean
(α : Type u) → Type u
```

Definition body (one-level semantic boundary):

```lean
fun α => α → Prop
```

### D047: `Set.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5858be77d319c5a0e238602f16818ed6fb2e2b52a81ff7edb07bc219d652f201`

Type:

```lean
{α : Type u} → Membership α (Set α)
```

Fully explicit type:

```lean
{α : Type u} → Membership.{u, u} α (Set.{u} α)
```

Definition body (one-level semantic boundary):

```lean
fun {α} => { mem := Set.Mem }
```

### D048: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D049: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```
