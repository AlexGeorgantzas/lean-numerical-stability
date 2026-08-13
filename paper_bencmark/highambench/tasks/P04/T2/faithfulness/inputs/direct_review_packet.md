# Declaration dossier for P04-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p04_t2_mixed_input_product_bound
    (uLow uFma u : ℝ) (q n : ℕ)
    (a b Δa Δb e computed : ℝ)
    (huLow : 0 ≤ uLow) (huFma : 0 ≤ uFma) (hu : 0 ≤ u)
    (hq : GammaValid uFma q) (hn : GammaValid u n)
    (hΔa : |Δa| ≤ uLow * |a|)
    (hΔb : |Δb| ≤ uLow * |b|)
    (he : |e| ≤ p04BlockFmaCoeff uFma u q n * |a + Δa| * |b + Δb|)
    (hcomputed : computed = (a + Δa) * (b + Δb) + e) :
    |computed - a * b| ≤
      (2 * uLow + uLow ^ 2 +
          p04BlockFmaCoeff uFma u q n * (1 + uLow) ^ 2) *
        |a| * |b|
```

## Elaborated target type

```lean
∀ (uLow uFma u : Real) (q n : Nat) (a b Δa Δb e computed : Real),
  Real.instLE.le 0 uLow →
    Real.instLE.le 0 uFma →
      Real.instLE.le 0 u →
        HighamBench.GammaValid uFma q →
          HighamBench.GammaValid u n →
            Real.instLE.le (abs Δa) (instHMul.hMul uLow (abs a)) →
              Real.instLE.le (abs Δb) (instHMul.hMul uLow (abs b)) →
                Real.instLE.le (abs e)
                    (instHMul.hMul (instHMul.hMul (HighamBench.p04BlockFmaCoeff uFma u q n) (abs (instHAdd.hAdd a Δa)))
                      (abs (instHAdd.hAdd b Δb))) →
                  Eq computed (instHAdd.hAdd (instHMul.hMul (instHAdd.hAdd a Δa) (instHAdd.hAdd b Δb)) e) →
                    Real.instLE.le (abs (instHSub.hSub computed (instHMul.hMul a b)))
                      (instHMul.hMul
                        (instHMul.hMul
                          (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 uLow) (instHPow.hPow uLow 2))
                            (instHMul.hMul (HighamBench.p04BlockFmaCoeff uFma u q n)
                              (instHPow.hPow (instHAdd.hAdd 1 uLow) 2)))
                          (abs a))
                        (abs b))
```

## Fully explicit elaborated target type

```lean
∀ (uLow uFma u : Real) (q n : Nat) (a b Δa Δb e computed : Real)
  (huLow : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uLow)
  (huFma : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uFma)
  (hu : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u)
  (hq : HighamBench.GammaValid uFma q) (hn : HighamBench.GammaValid u n)
  (hΔa :
    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup Δa)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) uLow
        (@abs.{0} Real Real.lattice Real.instAddGroup a)))
  (hΔb :
    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup Δb)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) uLow
        (@abs.{0} Real Real.lattice Real.instAddGroup b)))
  (he :
    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup e)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (HighamBench.p04BlockFmaCoeff uFma u q n)
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a Δa)))
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b Δb))))
  (hcomputed :
    @Eq.{1} Real computed
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a Δa)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b Δb))
        e)),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) computed
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a b)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              uLow)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              uLow (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (HighamBench.p04BlockFmaCoeff uFma u q n)
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) uLow)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@abs.{0} Real Real.lattice Real.instAddGroup a))
      (@abs.{0} Real Real.lattice Real.instAddGroup b))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P04Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P04Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.GammaValid`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `651ef903a8d9a3c8f539284f6c70325cebe6e199aad808cb56d9123f31e258c9`

Type:

```lean
Real → Nat → Prop
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u n => Real.instLT.lt (instHMul.hMul n.cast u) 1
```

### D002: `HighamBench.p04BlockFmaCoeff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7829a2958439fc05b0c2715ff1c5b4140cff6f33dd06568386434b5f6a25252a`

Type:

```lean
Real → Real → Nat → Nat → Real
```

Fully explicit type:

```lean
(uFma u : Real) → (q n : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun uFma u q n =>
  instHAdd.hAdd (instHAdd.hAdd (HighamBench.gamma uFma q) (HighamBench.gamma u n))
    (instHMul.hMul (HighamBench.gamma uFma q) (HighamBench.gamma u n))
```

### D003: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

Type:

```lean
Real → Nat → Real
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D004: `Eq`

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

### D005: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `2c99a1926bdac64e3a35f3fa155d689dc336fe4eb783a294540e765003beae74`

Hash-verified prior interpretation:

HAdd.hAdd selects the heterogeneous-addition operation supplied by its typeclass instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `8915b03a91c892e98db02c0973c28bad864cb016b465642b346d14f34e446a76`

Hash-verified prior interpretation:

HMul.hMul selects the heterogeneous-multiplication operation supplied by its typeclass instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D008: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `b332fe28eda7461a55409befd08f414509b9cfcdfd7730a06048da7b83c87c62`

Hash-verified prior interpretation:

HSub.hSub selects the heterogeneous-subtraction operation supplied by its instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `c476dc1b2ea074ec4bd39cbce7c0ff24c628f572b131686eb6963c3e7131fb19`

Hash-verified prior interpretation:

LE.le selects the non-strict order relation supplied for the type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D011: `Nat`

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

### D012: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `309ef94c4b7cfbe2e668952e6915279353921d5d48b6123a30f90dd932dac3e6`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

Fully explicit type:

```lean
∀ (n : Nat) [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n],
  Nat.AtLeastTwo
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D013: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`
- Semantic SHA-256: `a0735a528184c05594c4c79312c1225bb4dcffcdf0df7eb1a50c5733047c85ad`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ {n : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D014: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `37f0ecf64bd742bcc93f38034359021b711500e02dfff8ff3c1f2db70c293777`

Hash-verified prior interpretation:

OfNat.ofNat interprets a natural-number literal in the requested type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`
- Reuse SHA-256: `decd674803aac02ebd385212bdf204f6212acc91345ee72dc5ad8d7b3dfe3bb0`

Hash-verified prior interpretation:

One.toOfNat1 turns a One instance into the OfNat instance for the literal 1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `3483e25ab144d9f6b5fc2cc409de11ee2b17d27a19ada9ad855dd312dd9e9444`

Hash-verified prior interpretation:

Real is mathlib's type of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `2600632309109b9eef72c7a64a51bb9f19137f042a46f93146279b789a7082de`

Hash-verified prior interpretation:

Real.instAdd supplies ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `1f5c2cb2573ac7ae1df7dd2fb4169025e230cf39eed10a3bb6015178c0a216f9`

Hash-verified prior interpretation:

Real.instAddGroup supplies the additive-group structure on Real, including negation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `96f4d2c6a6ed1a6072650c127a11af0743154b941d6d0bf8072e93589cecd9d1`

Hash-verified prior interpretation:

Real.instLE supplies the usual non-strict order on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D021: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `cc1d87e896e40ca98beaba733d8981b2be417bf56b3cd139099a7fe33f462ebe`

Hash-verified prior interpretation:

Real.instMul supplies ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`
- Reuse SHA-256: `11515d289291036cdc99fffdf3a5fc5b207622a159829c92fabab8dbc5d90b0b`

Hash-verified prior interpretation:

Real.instNatCast supplies the canonical embedding of Nat into Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`
- Reuse SHA-256: `278b68069fb2dca8c3606f359ce8d431c0f9e00fb8e417d19697eed49e4fc22e`

Hash-verified prior interpretation:

Real.instOne supplies the multiplicative identity 1 in Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `b749cd229005c3a1648902abc2bc67a4c2a7c085861f5f029cae4ef461a4036c`

Hash-verified prior interpretation:

Real.instSub supplies ordinary real subtraction a-b=a+(-b).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `ca3e97a9097116b9d22990f2a068cbdfe0d452830107525cf6415bfebfc4c640`

Hash-verified prior interpretation:

Real.instZero supplies the additive identity 0 in Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `094296f36b8f60f6e248ebe56a2c9cd0a87d2a95d53003f3fb7fc76713aa00a8`

Hash-verified prior interpretation:

Real.lattice supplies max and min under the usual real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `dcd0bbc3c9d1e1b585248a4bf599d7d44121a8aebc485d3a81d91f3be94fc097`

Hash-verified prior interpretation:

Zero.toOfNat0 turns a Zero instance into the OfNat instance for the literal 0.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `32a708fd3378d4db96640e2e6509634aa96151e94172fcf7f08b2b9a3e3d8a93`

Hash-verified prior interpretation:

abs a is max(a,-a), hence standard absolute value on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `8f153af5aa1baf5f6424ff39c5d08323cd358ffeece5f9ced3043ad2cffa73b6`

Hash-verified prior interpretation:

instHAdd lifts a homogeneous Add operation to HAdd.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `46765db2b9c4e049bf61e51bed5aa60e6f7c8d1bae634a71be3cc3d75d34fb61`

Hash-verified prior interpretation:

instHMul lifts a homogeneous Mul operation to HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D032: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `f39a60e5a7fdc34f852de226b72fe543dea9c623443daecb3a67b84708f713fb`

Hash-verified prior interpretation:

instHSub lifts homogeneous subtraction to HSub.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D034: `instOfNatNat`

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

### D035: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`
- Reuse SHA-256: `8b6f0ef55849bf1625a675effbde90e63e8db4a1f7a2a09442af8969b6e8c3b6`

Hash-verified prior interpretation:

LT.lt selects the strict-order relation supplied for the type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`
- Reuse SHA-256: `fb2cb8ca958b6b9b06056213ea79965d590b2ebafdc4f8f0a3e9756bb034f7d8`

Hash-verified prior interpretation:

Nat.cast maps a natural number to the corresponding value in a type with NatCast.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`
- Reuse SHA-256: `03d17dba89598f99d38453fd511ae8ed17b425a007576df0a782595ade0fc63c`

Hash-verified prior interpretation:

Real.instLT supplies the usual strict order on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `df63d67be0a47651e461c7c0857bc6f06de6eb2312aa865ec12586eb832a6aa4`

Hash-verified prior interpretation:

DivInvMonoid.toDiv extracts the division operation from a division/inverse monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `7cc520200fbbc81cb5af9bd69f23a7fa8d3c03985e9622d43e610579ec2d1769`

Hash-verified prior interpretation:

HDiv.hDiv selects the heterogeneous-division operation supplied by its instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `ab4d730c0e1a3194e52e83a676c0de91daf486521f7cb16d7cf21b77a11bde44`

Hash-verified prior interpretation:

Real.instDivInvMonoid supplies real multiplication, inverse, and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D041: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `bf79a894f33a6eb637c4e4c038bf278981a5dc8a3e147af4deafafc35a9b734c`

Hash-verified prior interpretation:

instHDiv lifts homogeneous division to HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
