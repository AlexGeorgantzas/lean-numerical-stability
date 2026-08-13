# Declaration dossier for P03-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p03_t3_componentwise_residual_recurrence
    {n : ℕ} (us u gammaR : ℝ)
    (M1 P : Fin n → Fin n → ℝ)
    (oldResidual data update correction newResidual : Fin n → ℝ)
    (hresolvent : P03ResolventInverse M1 P)
    (hcorrection : ∀ i : Fin n,
      correction i ≤ p03MatVec P correction i +
        ((1 + us) * |oldResidual i| +
          (1 + us) * (1 + u) * gammaR * data i))
    (hbase : ∀ i : Fin n,
      |newResidual i| ≤
        us * |oldResidual i| +
          (1 + us) * (1 + u) * gammaR * data i +
          correction i + u * update i) :
    ∀ i : Fin n,
      |newResidual i| ≤
        us * |oldResidual i| +
          (1 + us) * p03MatVec M1 (p03VecAbs oldResidual) i +
          (1 + us) * (1 + u) * gammaR *
            (data i + p03MatVec M1 data i) +
          u * update i
```

## Elaborated target type

```lean
∀ {n : Nat} (us u gammaR : Real) (M1 P : Fin n → Fin n → Real)
  (oldResidual data update correction newResidual : Fin n → Real),
  HighamBench.P03ResolventInverse M1 P →
    (∀ (i : Fin n),
        Real.instLE.le (correction i)
          (instHAdd.hAdd (HighamBench.p03MatVec P correction i)
            (instHAdd.hAdd (instHMul.hMul (instHAdd.hAdd 1 us) (abs (oldResidual i)))
              (instHMul.hMul (instHMul.hMul (instHMul.hMul (instHAdd.hAdd 1 us) (instHAdd.hAdd 1 u)) gammaR)
                (data i))))) →
      (∀ (i : Fin n),
          Real.instLE.le (abs (newResidual i))
            (instHAdd.hAdd
              (instHAdd.hAdd
                (instHAdd.hAdd (instHMul.hMul us (abs (oldResidual i)))
                  (instHMul.hMul (instHMul.hMul (instHMul.hMul (instHAdd.hAdd 1 us) (instHAdd.hAdd 1 u)) gammaR)
                    (data i)))
                (correction i))
              (instHMul.hMul u (update i)))) →
        ∀ (i : Fin n),
          Real.instLE.le (abs (newResidual i))
            (instHAdd.hAdd
              (instHAdd.hAdd
                (instHAdd.hAdd (instHMul.hMul us (abs (oldResidual i)))
                  (instHMul.hMul (instHAdd.hAdd 1 us) (HighamBench.p03MatVec M1 (HighamBench.p03VecAbs oldResidual) i)))
                (instHMul.hMul (instHMul.hMul (instHMul.hMul (instHAdd.hAdd 1 us) (instHAdd.hAdd 1 u)) gammaR)
                  (instHAdd.hAdd (data i) (HighamBench.p03MatVec M1 data i))))
              (instHMul.hMul u (update i)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (us u gammaR : Real) (M1 P : Fin n → Fin n → Real)
  (oldResidual data update correction newResidual : Fin n → Real) (hresolvent : @HighamBench.P03ResolventInverse n M1 P)
  (hcorrection :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE (correction i)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p03MatVec n P correction i)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) us)
              (@abs.{0} Real Real.lattice Real.instAddGroup (oldResidual i)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) us)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u))
                gammaR)
              (data i)))))
  (hbase :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (newResidual i))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) us
                (@abs.{0} Real Real.lattice Real.instAddGroup (oldResidual i)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) us)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u))
                  gammaR)
                (data i)))
            (correction i))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u (update i))))
  (i : Fin n),
  @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (newResidual i))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) us
            (@abs.{0} Real Real.lattice Real.instAddGroup (oldResidual i)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) us)
            (@HighamBench.p03MatVec n M1 (@HighamBench.p03VecAbs n oldResidual) i)))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) us)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u))
            gammaR)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (data i)
            (@HighamBench.p03MatVec n M1 data i))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u (update i)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P03Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P03Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P03ResolventInverse`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `936b0a52656f6517463d3ac6f688297989610099bda0819bd2926d8896a7cb82`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (M P : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} M P =>
  And (∀ (i k : Fin n), Real.instLE.le 0 (M i k))
    (∀ (z : Fin n → Real) (i : Fin n),
      Eq (HighamBench.p03MatVec M (fun k => instHSub.hSub (z k) (HighamBench.p03MatVec P z k)) i) (z i))
```

### D002: `HighamBench.p03MatVec`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `1369ded3dc793c70d72eeba99084d1d0ffc9aac01ed5047bab8b80574697ee32`
- Reuse SHA-256: `3f3e080f083006263af0420142bb13cab74424b883a0dbb86672ce9986c4f184`

Hash-verified prior interpretation:

For row i, p03MatVec A v i is the finite real sum over columns j of A i j multiplied by v j.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D003: `HighamBench.p03VecAbs`

- Role: `local`
- Owner module: `HighamBench.P03Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cbcbc1d3ff3dbe2170b57b8eb1dc87d4298806361ceb82cf64cda83fcd35d815`

Type:

```lean
{n : Nat} → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x i => abs (x i)
```

### D004: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `d6ff16e3d0dd2d5208f716846c88566e2cda555104a5ef994744bbc9fe3b964c`

Hash-verified prior interpretation:

Fin n is the finite coordinate index type with indices from zero through n minus one.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `f0a208134f0be8d9c4f62fed752e833defbeaa7d7355a7f0eb97527b52a769f8`

Hash-verified prior interpretation:

HAdd.hAdd dispatches overloaded addition through the selected HAdd instance; here it resolves to real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `043f9e8718f9e88882d760a34b86e7840facb49adb85e336d277391509a74cc5`

Hash-verified prior interpretation:

HMul.hMul dispatches overloaded multiplication through the selected HMul instance; here it resolves to real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D008: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `a9b35dc65f8fe1414c7c158021712de6bc81e36dfed74f53b6ef0e77d99649a9`

Hash-verified prior interpretation:

Nat is the type of natural numbers used for the system dimension n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Fully explicit type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat.{u} α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D010: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D011: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `ea1c9703299f6b4a3989c797f2a9a0a1b79aaf14813b3322023661d8f3fd7482`

Hash-verified prior interpretation:

Real is Lean's exact mathematical real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `b99f49fd674e6c7b3215be434e704ba83bdf1057272a73d2ff3a7bde1d80f163`

Hash-verified prior interpretation:

Real.instAdd provides ordinary addition on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`

Type:

```lean
AddGroup Real
```

Fully explicit type:

```lean
AddGroup.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D014: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`

Type:

```lean
LE Real
```

Fully explicit type:

```lean
LE.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D015: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `fc791f7590243b52a697d21d3fbd5944209c68022bbf93965ff90e52c8064ff0`

Hash-verified prior interpretation:

Real.instMul provides ordinary multiplication on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D017: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`

Type:

```lean
Lattice Real
```

Fully explicit type:

```lean
Lattice.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D018: `abs`

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

### D019: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `562d1a77e6f0776269d696792195dd2231b029682f446a852186626214a6bcea`

Hash-verified prior interpretation:

instHAdd lifts a homogeneous Add instance into a homogeneous HAdd instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `5cb07b0c605f9c2b2762be4698a32090340f3fde3d71d965a362602ee4972b70`

Hash-verified prior interpretation:

instHMul lifts a homogeneous Mul instance into a homogeneous HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D022: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `32b960214ea75a7ddf0ac041367800a710306055c759f30a565b31620dab305a`

Hash-verified prior interpretation:

Eq is exact propositional equality between two terms of the same type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `9778af6807090f8be77da7856f20df1359a48e3eabbf5177f68b8be8f96a9e7b`

Hash-verified prior interpretation:

Fin.fintype supplies a finite enumeration containing every element of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `6baae77808ea118cc1051b8c696d042b6b9355aebb6ea48b33ab2fd4b3154686`

Hash-verified prior interpretation:

Finset.sum folds an AddCommMonoid-valued function over a finite set, using zero for the empty sum.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `656630b2582fd6cba8097035767a9c99111e207d64db5ae8aed7d38a9c748437`

Hash-verified prior interpretation:

Finset.univ is the finite set of all elements of a fintype.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `9017c277d92c5358fe64cc0ef2804adaebdf76bdd631d915f904d1c3979a83da`

Hash-verified prior interpretation:

HSub.hSub dispatches overloaded subtraction through the selected HSub instance; here it resolves to real subtraction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `45d4fe3a9ca198b001b264d2e14a6ccc6b85181a512993edb6d0f479bda740b1`

Hash-verified prior interpretation:

Real.instAddCommMonoid is the usual commutative additive monoid structure on the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `03ad41775b4bca106588bd3e220fadb0dbf2a8375d5ebfe25f82138c181b8bf6`

Hash-verified prior interpretation:

Real.instSub defines real subtraction as addition of the additive inverse.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D030: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D031: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `ccbdd5ce3779363286f65e5e9de8f087e59f2fc61339cf8cba930745ac59120f`

Hash-verified prior interpretation:

instHSub lifts a homogeneous Sub instance into a homogeneous HSub instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
