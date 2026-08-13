# Declaration dossier for P08-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p08_t2_lemma_4_2_residual_bound
    {n : ℕ} (A Ainv : Fin n → Fin n → ℝ)
    (x q h xNext : Fin n → ℝ) (u : ℝ)
    (hu : 0 ≤ u)
    (hInverseAction : ∀ i, p08MatVec A (p08MatVec Ainv q) i = q i)
    (hUpdate : ∀ i, xNext i = p08MatVec Ainv q i + x i + h i)
    (hRound : ∀ i, |h i| ≤ u * |p08MatVec Ainv q i| + u * |x i|) :
    ∀ i, |p08MatVec A (fun j ↦ xNext j - x j) i| ≤
      |q i| + u * p08AbsProductAction A Ainv q i +
        u * p08AbsAction A x i
```

## Elaborated target type

```lean
∀ {n : Nat} (A Ainv : Fin n → Fin n → Real) (x q h xNext : Fin n → Real) (u : Real),
  Real.instLE.le 0 u →
    (∀ (i : Fin n), Eq (HighamBench.p08MatVec A (HighamBench.p08MatVec Ainv q) i) (q i)) →
      (∀ (i : Fin n), Eq (xNext i) (instHAdd.hAdd (instHAdd.hAdd (HighamBench.p08MatVec Ainv q i) (x i)) (h i))) →
        (∀ (i : Fin n),
            Real.instLE.le (abs (h i))
              (instHAdd.hAdd (instHMul.hMul u (abs (HighamBench.p08MatVec Ainv q i))) (instHMul.hMul u (abs (x i))))) →
          ∀ (i : Fin n),
            Real.instLE.le (abs (HighamBench.p08MatVec A (fun j => instHSub.hSub (xNext j) (x j)) i))
              (instHAdd.hAdd (instHAdd.hAdd (abs (q i)) (instHMul.hMul u (HighamBench.p08AbsProductAction A Ainv q i)))
                (instHMul.hMul u (HighamBench.p08AbsAction A x i)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A Ainv : Fin n → Fin n → Real) (x q h xNext : Fin n → Real) (u : Real)
  (hu : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u)
  (hInverseAction : ∀ (i : Fin n), @Eq.{1} Real (@HighamBench.p08MatVec n A (@HighamBench.p08MatVec n Ainv q) i) (q i))
  (hUpdate :
    ∀ (i : Fin n),
      @Eq.{1} Real (xNext i)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@HighamBench.p08MatVec n Ainv q i)
            (x i))
          (h i)))
  (hRound :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (h i))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
            (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p08MatVec n Ainv q i)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
            (@abs.{0} Real Real.lattice Real.instAddGroup (x i)))))
  (i : Fin n),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HighamBench.p08MatVec n A
        (fun (j : Fin n) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (xNext j) (x j)) i))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@abs.{0} Real Real.lattice Real.instAddGroup (q i))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u
          (@HighamBench.p08AbsProductAction n A Ainv q i)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u (@HighamBench.p08AbsAction n A x i)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P08Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P08Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p08AbsAction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `2e411afdeeff87e69866a73e67fc559f4099fa28d728bac01a806d5050ad1e33`
- Reuse SHA-256: `9312d8d67292851981e077b9b906eaaa80a587f9a7bcee67ab2ef5772313a284`

Hash-verified prior interpretation:

For component i, this is the finite sum over j of |A i j| * |x j|.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D002: `HighamBench.p08AbsProductAction`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `ffeaac0c0c40a7ab5550f742b33989fbd8f717c5e527e498865e1ad74ddd6346`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : Fin n → Fin n → Real) → (q : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv q i => Finset.univ.sum fun j => instHMul.hMul (abs (A i j)) (HighamBench.p08AbsAction Ainv q j)
```

### D003: `HighamBench.p08MatVec`

- Role: `local`
- Owner module: `HighamBench.P08Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `a592839d471927bb3cc257d8a1d685487e1a3d3378b7ad9ee731c33e3c99b742`
- Reuse SHA-256: `a9d79755c0b741985d1e1e0ca415db594fe3f827e5671d0f293263ace774c268`

Hash-verified prior interpretation:

For component i, this is the exact real finite sum over j of A i j * x j.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `4738cba5cc594bbac3846d1c19e331eb0252249c7384087d8d0e03e992b0abe2`

Hash-verified prior interpretation:

Lean propositional equality between two values of the same type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `96e15d871d236cbc25d682c9f570695df429e2face86e6d3528c4bce81cf3b23`

Hash-verified prior interpretation:

Fin n is the finite type of component indices below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `f13ed12686614b6b31fc7607b2d23f1e6345c9af7590f67f762968a359a927c3`

Hash-verified prior interpretation:

Typeclass-dispatched heterogeneous addition, instantiated here as ordinary real addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `e466488d860a5eb0bad0d927ad481fd0e7c12861a111ea87d5f95c1bcd3dedf5`

Hash-verified prior interpretation:

Typeclass-dispatched heterogeneous multiplication, instantiated here as ordinary real multiplication.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `31db7f3ecb506e7ffc29045a406485625004c8dcdef47f7046a4173975d607a3`

Hash-verified prior interpretation:

Typeclass-dispatched heterogeneous subtraction, instantiated here as ordinary real subtraction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `e434ed303905a7af228ce4b9d1a15569ffa23968bcfe5126a8808f75a8ac6fbb`

Hash-verified prior interpretation:

Typeclass-dispatched non-strict order, instantiated here as the usual real less-than-or-equal relation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `426cf73e510c14035682ac468bdf1b9cf2b3f9df8af96c0b89108ec6b97b7bc8`

Hash-verified prior interpretation:

The natural-number type used for the finite dimension n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `3454ad265d13962382c545c60fc41a17008f880814dce746a3fbfc561629609f`

Hash-verified prior interpretation:

Conversion of natural-number literals to the target numeric type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `3273e6ddd8bd4a8443707638cde935852e5da6c599a38a8fe3930f2970ac1f22`

Hash-verified prior interpretation:

Mathlib's mathematical real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `7e0ddf4261b358fe7b8c14711ff101f8751ed922fe7477e2df915734becc8a90`

Hash-verified prior interpretation:

The standard addition operation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `ff0528324617b8360c8762e233843aae601952bd850aaffbb43e9c41e8131cd4`

Hash-verified prior interpretation:

The standard additive-group structure on the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `def617339f069ce01d94636c7b9c556e50dfc215659e7b4ee9b5aae462d53615`

Hash-verified prior interpretation:

The standard total-order less-than-or-equal relation on the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `aaec7186856181049f8d1bbf0329e413c2961f70d69ca90a7251c23b1b81760e`

Hash-verified prior interpretation:

The standard multiplication operation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `f36832743660c512909e56a0953d385505528776a493e0dff10ead99add35b47`

Hash-verified prior interpretation:

Standard real subtraction, implemented as addition of the real negation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `ebc699a0ada091fb712ded556742b0e7d49aaf0bbe071cac139061ca9d6e2f2c`

Hash-verified prior interpretation:

The standard additive identity of the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `e3ae9be753d2d5bb3d635ed3eb9a07b4912ede6780709f00522a9ce1aa5f0a1f`

Hash-verified prior interpretation:

The standard lattice structure induced by the real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `f96c37bd331eb23dd809632bd2891f417408c19de2b341340340563a78eb24d4`

Hash-verified prior interpretation:

It constructs the numeral-zero instance from the real additive identity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `47d8fbad79913ded62d049d8aba1c2b66e36e59e6bd2ff5b7e4d95a04f5a1e23`

Hash-verified prior interpretation:

In an ordered additive group this is max(a,-a), hence the usual real absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `c0a6a190798a2d1228f4f0bb8bbb90617d8a43deedb47658cd8c8c23ddcd20b1`

Hash-verified prior interpretation:

Adapter turning a homogeneous Add instance into the corresponding HAdd instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `c666e179ff29ed06a9928f75c04d36f7c4c995624033bd602aed763680d886fd`

Hash-verified prior interpretation:

Adapter turning a homogeneous Mul instance into the corresponding HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `a1992622cc64ff9ed888a9e2d1747f8c11f2e1830838db759ceadf691291f46e`

Hash-verified prior interpretation:

Adapter turning a homogeneous Sub instance into the corresponding HSub instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `8748c06d8f32dae7dc9ed5034f3e3bc762877aeb2dc067994584210549352429`

Hash-verified prior interpretation:

The finite enumeration of every element of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `43dbdf9bda2f29d93880e1dba6eeb528312c1541af4765b62b6df2ecd0f56459`

Hash-verified prior interpretation:

Finite summation in an additive commutative monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `a061e3638d96f1a31253c20b9ffa2eeb99276b1fe129ade0c88026022301173d`

Hash-verified prior interpretation:

The finite set containing every element of a finite type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `de26263ef3d85bea98d73430409944d56d7056e9e81a8b238a6dead7fd589944`

Hash-verified prior interpretation:

The standard additive commutative-monoid structure on the reals.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
