# Declaration dossier for P05-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p05_t3_cholesky_backward_error
    {n : ℕ} (u : ℝ)
    (A R : Fin n → Fin n → ℝ)
    (hu : 0 ≤ u)
    (hA_symm : ∀ i j, A i j = A j i)
    (hupper : ∀ i j, i.val ≤ j.val →
      |p05MatMul (p05Transpose R) R i j - A i j| ≤
        ((i.val + 2 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul (p05Transpose R) R = A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n + 1 : ℕ) : ℝ) * u *
          p05AbsMatMul (p05Transpose R) R i j
```

## Elaborated target type

```lean
∀ {n : Nat} (u : Real) (A R : Fin n → Fin n → Real),
  Real.instLE.le 0 u →
    (∀ (i j : Fin n), Eq (A i j) (A j i)) →
      (∀ (i j : Fin n),
          instLENat.le i.val j.val →
            Real.instLE.le (abs (instHSub.hSub (HighamBench.p05MatMul (HighamBench.p05Transpose R) R i j) (A i j)))
              (instHMul.hMul (instHMul.hMul (instHAdd.hAdd i.val 2).cast u)
                (HighamBench.p05AbsMatMul (HighamBench.p05Transpose R) R i j))) →
        Exists fun ΔA =>
          And (Eq (HighamBench.p05MatMul (HighamBench.p05Transpose R) R) (instHAdd.hAdd A ΔA))
            (And
              (∀ (i j : Fin n),
                Real.instLE.le (abs (ΔA i j))
                  (instHMul.hMul (instHMul.hMul (instHAdd.hAdd i.val 2).cast u)
                    (HighamBench.p05AbsMatMul (HighamBench.p05Transpose R) R i j)))
              (∀ (i j : Fin n),
                Real.instLE.le (abs (ΔA i j))
                  (instHMul.hMul (instHMul.hMul (instHAdd.hAdd n 1).cast u)
                    (HighamBench.p05AbsMatMul (HighamBench.p05Transpose R) R i j))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (u : Real) (A R : Fin n → Fin n → Real)
  (hu : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u)
  (hA_symm : ∀ (i j : Fin n), @Eq.{1} Real (A i j) (A j i))
  (hupper :
    ∀ (i j : Fin n),
      @LE.le.{0} Nat instLENat (@Fin.val n i) (@Fin.val n j) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HighamBench.p05MatMul n (@HighamBench.p05Transpose n R) R i j) (A i j)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              u)
            (@HighamBench.p05AbsMatMul n (@HighamBench.p05Transpose n R) R i j))),
  @Exists.{1} (Fin n → Fin n → Real) fun (ΔA : Fin n → Fin n → Real) =>
    And
      (@Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p05MatMul n (@HighamBench.p05Transpose n R) R)
        (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real) (Fin n → Fin n → Real) (Fin n → Fin n → Real)
          (@instHAdd.{0} (Fin n → Fin n → Real)
            (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Fin n → Real) fun (i : Fin n) =>
              @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
          A ΔA))
      (And
        (∀ (i j : Fin n),
          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                u)
              (@HighamBench.p05AbsMatMul n (@HighamBench.p05Transpose n R) R i j)))
        (∀ (i j : Fin n),
          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                u)
              (@HighamBench.p05AbsMatMul n (@HighamBench.p05Transpose n R) R i j))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P05Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P05Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p05AbsMatMul`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe75f4145e1b29dc797163b1c5e5bf58a54b99328abc1689fc23613d5d405671`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (abs (A i k)) (abs (B k j))
```

### D002: `HighamBench.p05MatMul`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8b658624127af1765d1831514845fbf3705f949e157d27c75ca6a03e4bd9cf19`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D003: `HighamBench.p05Transpose`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c98072df9e9b350096ec63ce7329d663300c9ad2c7358ac5d2f8a729a34d3102`

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

### D004: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`
- Reuse SHA-256: `fa901ab9fa0851be14d6c05cbed6852eb24e26e6b3b98733e1851c1a112b1589`

Hash-verified prior interpretation:

And requires all nested coefficient bounds and the final identity simultaneously.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `fac5876e66a474abbf232195a72044922c72557d6a8d69c191072cfc1228777d`

Hash-verified prior interpretation:

Eq is exact equality over Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`
- Reuse SHA-256: `b5a7d2275af795dac08bd22691293caf3334e383a8eafdd5f6e52e683ee6a012`

Hash-verified prior interpretation:

Exists introduces witnesses theta0, theta_c, and the indexed family theta_p.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `5875692f026d76e62fc26485858e7b1d9ce65ee66bb941ec5fd2061f377be9ce`

Hash-verified prior interpretation:

Fin k indexes exactly k values, represented by indices 0 through k-1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Fully explicit type:

```lean
{n : Nat} → (self : Fin n) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D009: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `9f056b2e5cbaaa14948afde8edde9e167324c8484cd74f28d83347c55207ccfe`

Hash-verified prior interpretation:

This resolves to natural addition for k + 1 and real addition for 1 + theta.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `40f0ae6adce5bf8c57f51853d941cb5d59710267fa6c2d315060276f9fa7a8ec`

Hash-verified prior interpretation:

This resolves to ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `19755e479ca7ef887f1af40be30d133d231eae8b917ff77854bc7bdf6acf37cc`

Hash-verified prior interpretation:

This resolves to ordinary real subtraction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `eeaf8c7a4905aea616484883fcf3053f921ba69a29aff63d5a44c9d2289c2fa5`

Hash-verified prior interpretation:

This is the non-strict order relation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `61ae1daf69f8e4e7332ddb1d499aab6977055cde931ebdc603af911f52b20238`

Hash-verified prior interpretation:

Nat permits k = 0 and all positive natural values.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`
- Reuse SHA-256: `642f2a2071ee54aac6186174cd81113a34f1a3f56a3d00c5c7b67f0106b81029`

Hash-verified prior interpretation:

Nat.cast embeds k + 1 into Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `7b725188cc5e00e20f6ebfa4ce4bcaf3cbe9ad773d385f0d46939a775a35d805`

Hash-verified prior interpretation:

This supplies the numeric literals 0 and 1 in their inferred types.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add.{u_5} (M i)] → Add.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D017: `Real`

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

### D018: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `2d930d4b5acf4034ea9ee6d8b9abdf4599e207555e4835885739be5400145ed2`

Hash-verified prior interpretation:

This is ordinary addition on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `d3c51d07544cc34f1f42a0e704106411aa4811e3ae1c7abcf6a7f969e8c06700`

Hash-verified prior interpretation:

This supplies real addition, negation, subtraction, and the group structure used by abs.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `1d7220e5efc4be1f955289cc55805de717ccfc4582dcc205501c1be282a13533`

Hash-verified prior interpretation:

This is the usual total order on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `5bb3ef339a1edc6e149ecc012091103f2d31bed0c15fa04ae85afb2fa3b7b68f`

Hash-verified prior interpretation:

This is ordinary multiplication on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`
- Reuse SHA-256: `f94e129edc87824e7c814e74a0289f409e0aa69bffa0dff5a8758e92c4f3bbb4`

Hash-verified prior interpretation:

This maps a natural number to its corresponding nonnegative real integer.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `15d7f43dd3752ca576ca23d2889ed914e19652df1a82de1049f67d3f06602d01`

Hash-verified prior interpretation:

Real subtraction is addition of the additive inverse.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `4506affb4026db816ad3e51d1fd339303d70b1621c4ae39272b7a1a098d3c479`

Hash-verified prior interpretation:

This supplies real zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `a1906d0e20cf585ff30c2128111859b93cad2725355e2abd58a0333ba1b7b9fa`

Hash-verified prior interpretation:

This supplies the real lattice operations used to define absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `d437ddea9ddcc208b0277e361d9364995316017678010c4dd60ad81b88ee3207`

Hash-verified prior interpretation:

This derives the numeral 0 from the relevant Zero instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `890b5f59077062794363238e8ced83e50aa0c0570caeaefb6aa5236aa634c169`

Hash-verified prior interpretation:

For Real, abs a is max(a, -a), the standard scalar absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`
- Reuse SHA-256: `c2154f67232ffd34f5d2f42011e617abd8756da6fd4a5d0b57372c9661ee8c0e`

Hash-verified prior interpretation:

This is ordinary natural-number addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `20abbb44bbcb68937f620b7fcc50bdce795434a0f82b07010307717206e150a0`

Hash-verified prior interpretation:

This converts homogeneous Add instances into HAdd operations.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `4bde0db7e9151831dc5e088a81232b0ba20e704022902636b8109a25bfb2a49d`

Hash-verified prior interpretation:

This converts homogeneous Mul instances into HMul operations.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `6ed943d80a53918e83f3ea24f37167757326a223caac9d7a61342a07460f1b94`

Hash-verified prior interpretation:

This converts homogeneous Sub instances into HSub operations.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

Type:

```lean
LE Nat
```

Fully explicit type:

```lean
LE.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D033: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `d9ec66b2bc5079ce59d7730deafdad176327901bffaf63a29eb3c87a2deea0ac`

Hash-verified prior interpretation:

This interprets a natural numeral as that same natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `78cd10ac8520667ba7f35186fb24822b31325439e82f0e8b2d352377fddaea63`

Hash-verified prior interpretation:

This supplies the finite enumeration of Fin k.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `eed7b114f9de337dd3cf7ae0edbccfcba2dd7e93f80ccebdcfd96decc16746b0`

Hash-verified prior interpretation:

Finset.sum adds the image of every member of a finite set in the real additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `e31a8b1776a43e8485e6b6b2830177742bc6f9698a444f766faefda853c2f8ac`

Hash-verified prior interpretation:

Finset.univ contains every value of the relevant finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `96216297869121a481f2d2074c4d60a9f2b7f7a87338e5f32994911e0606e446`

Hash-verified prior interpretation:

This supplies Real's associative, commutative addition with zero for finite sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
