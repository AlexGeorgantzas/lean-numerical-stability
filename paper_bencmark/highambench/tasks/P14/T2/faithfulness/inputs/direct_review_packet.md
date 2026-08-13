# Declaration dossier for P14-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p14_t2_basic_softmax_component_error {n : ℕ}
    (fp : StandardAddModel) (x wHat : Fin n → ℝ) (j : Fin n)
    (epsilonExp epsilonDiv deltaDiv : ℝ)
    (hepsilonExp : 0 ≤ epsilonExp)
    (hepsilonDiv : 0 ≤ epsilonDiv)
    (hdeltaDiv : |deltaDiv| ≤ epsilonDiv)
    (hwHat : ∀ i, 0 ≤ wHat i)
    (hexp : ∀ i,
      |wHat i - Real.exp (x i)| ≤ epsilonExp * Real.exp (x i))
    (hvalid : GammaValid fp.u n)
    (hsmall : p14DenominatorRadius fp.u n epsilonExp < 1) :
    |p14ComputedSoftmax fp wHat deltaDiv j - p14Softmax x j| /
        |p14Softmax x j| ≤
      (p14NumeratorRadius epsilonExp epsilonDiv +
          p14DenominatorRadius fp.u n epsilonExp) /
        (1 - p14DenominatorRadius fp.u n epsilonExp)
```

## Elaborated target type

```lean
∀ {n : Nat} (fp : HighamBench.StandardAddModel) (x wHat : Fin n → Real) (j : Fin n)
  (epsilonExp epsilonDiv deltaDiv : Real),
  Real.instLE.le 0 epsilonExp →
    Real.instLE.le 0 epsilonDiv →
      Real.instLE.le (abs deltaDiv) epsilonDiv →
        (∀ (i : Fin n), Real.instLE.le 0 (wHat i)) →
          (∀ (i : Fin n),
              Real.instLE.le (abs (instHSub.hSub (wHat i) (Real.exp (x i))))
                (instHMul.hMul epsilonExp (Real.exp (x i)))) →
            HighamBench.GammaValid fp.u n →
              Real.instLT.lt (HighamBench.p14DenominatorRadius fp.u n epsilonExp) 1 →
                Real.instLE.le
                  (instHDiv.hDiv
                    (abs
                      (instHSub.hSub (HighamBench.p14ComputedSoftmax fp wHat deltaDiv j) (HighamBench.p14Softmax x j)))
                    (abs (HighamBench.p14Softmax x j)))
                  (instHDiv.hDiv
                    (instHAdd.hAdd (HighamBench.p14NumeratorRadius epsilonExp epsilonDiv)
                      (HighamBench.p14DenominatorRadius fp.u n epsilonExp))
                    (instHSub.hSub 1 (HighamBench.p14DenominatorRadius fp.u n epsilonExp)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (fp : HighamBench.StandardAddModel) (x wHat : Fin n → Real) (j : Fin n)
  (epsilonExp epsilonDiv deltaDiv : Real)
  (hepsilonExp :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonExp)
  (hepsilonDiv :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonDiv)
  (hdeltaDiv : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup deltaDiv) epsilonDiv)
  (hwHat :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (wHat i))
  (hexp :
    ∀ (i : Fin n),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (wHat i) (Real.exp (x i))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilonExp (Real.exp (x i))))
  (hvalid : HighamBench.GammaValid (HighamBench.StandardAddModel.u fp) n)
  (hsmall :
    @LT.lt.{0} Real Real.instLT (HighamBench.p14DenominatorRadius (HighamBench.StandardAddModel.u fp) n epsilonExp)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HighamBench.p14ComputedSoftmax n fp wHat deltaDiv j) (@HighamBench.p14Softmax n x j)))
      (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p14Softmax n x j)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (HighamBench.p14NumeratorRadius epsilonExp epsilonDiv)
        (HighamBench.p14DenominatorRadius (HighamBench.StandardAddModel.u fp) n epsilonExp))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (HighamBench.p14DenominatorRadius (HighamBench.StandardAddModel.u fp) n epsilonExp)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P14Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P14Definitions` imports: `HighamBench.Core`

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

### D002: `HighamBench.StandardAddModel`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `inductive`
- Semantic SHA-256: `3af55263a5df34d0cebe2443070580aacd6049ec653e6aa810dee85f7d8da3b8`
- Reuse SHA-256: `c7e2491e5f63703e2a7d0e1f88eb3d60ed87130d1bcd6602b7ab7c87a2f9da63`

Hash-verified prior interpretation:

This structure packages a nonnegative real unit roundoff, a real binary addition operation, exact addition from a left zero, and a relative-error witness for every pair of operands.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D003: `HighamBench.StandardAddModel.u`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Semantic SHA-256: `c64c9c9e28b3861652ba7445f856da30d4b2e48822f5710fa9e1e9bcf81ad0a8`
- Reuse SHA-256: `497c8bacab6953e86597201301e5e4f40e96159de56a86ce0e2d55c58108d131`

Hash-verified prior interpretation:

This projection returns the real unit-roundoff parameter of the addition model.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p14ComputedSoftmax`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a5f663425c9c5ace0d2e225cbac1cc3fe167019c0a1ddd3c8ee4ef35a75e0457`

Type:

```lean
{n : Nat} → HighamBench.StandardAddModel → (Fin n → Real) → Real → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (fp : HighamBench.StandardAddModel) → (wHat : Fin n → Real) → (deltaDiv : Real) → (j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} fp wHat deltaDiv j =>
  instHMul.hMul (instHDiv.hDiv (wHat j) (HighamBench.recursiveSum fp.fl_add n wHat)) (instHAdd.hAdd 1 deltaDiv)
```

### D005: `HighamBench.p14DenominatorRadius`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `e772c37d67881c0ea7bc7a63a19a63ac4af16d78955abdad80299f1bcf5e9495`

Type:

```lean
Real → Nat → Real → Real
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → (epsilonExp : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n epsilonExp => instHAdd.hAdd epsilonExp (instHMul.hMul (HighamBench.gamma u n) (instHAdd.hAdd 1 epsilonExp))
```

### D006: `HighamBench.p14NumeratorRadius`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `0b566c95c9cac0bf5241197f66f68357502c9a5edc2b073ce93837b025f883d5`

Type:

```lean
Real → Real → Real
```

Fully explicit type:

```lean
(epsilonExp epsilonDiv : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun epsilonExp epsilonDiv => instHAdd.hAdd (instHAdd.hAdd epsilonExp epsilonDiv) (instHMul.hMul epsilonExp epsilonDiv)
```

### D007: `HighamBench.p14Softmax`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a853928431944e72daa32c487281f619ec30b4f6f97ebd3a31f9d8f0ea020b03`

Type:

```lean
{n : Nat} → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → (j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x j => instHDiv.hDiv (Real.exp (x j)) (HighamBench.p14ExpSum x)
```

### D008: `HighamBench.StandardAddModel.fl_add`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Semantic SHA-256: `74b643970f719ee8bb48fde2f9970bb4c4568fb59d10e316bf1b16e3d35ea302`
- Reuse SHA-256: `4d67f12e73cd52ee61ededab8239bc269a49fb2cf51fab6bcfda7ca883bea11c`

Hash-verified prior interpretation:

This projection is the modeled rounded binary addition function stored in StandardAddModel.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HighamBench.StandardAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `constructor`
- Semantic SHA-256: `7d89a60d997fdb3f5928a4b754043bc2ff3d75d6af267762a5f86bdca796bc01`
- Reuse SHA-256: `81db07e5f6be3b9663f97baab2cc489aba9077f77bd6c6967c9c596af38c591e`

Hash-verified prior interpretation:

The constructor requires 0 <= u, fl_add 0 x = x, and for every x,y an operand-dependent delta with |delta| <= u and fl_add x y = (x+y)(1+delta).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `HighamBench.gamma`

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

### D011: `HighamBench.p14ExpSum`

- Role: `local`
- Owner module: `HighamBench.P14Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8f913d09c91e68ed49377c477b128a614150d79814d916fc11d9e5fe77b46368`

Type:

```lean
{n : Nat} → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x => Finset.univ.sum fun i => Real.exp (x i)
```

### D012: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Semantic SHA-256: `3a24e7a5c707c014d59b9d90d536db1f1c79ef135d2ba34adb6af8a4258efe41`
- Reuse SHA-256: `0b8ce2e45f1baf985a64ff0690a38e74c33f3683dda479147d6bb3bb7405809f`

Hash-verified prior interpretation:

For zero terms it returns 0, for one term it returns that term, and for at least two terms it recursively sums the prefix and applies flAdd to the final term.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Semantic SHA-256: `7f01e5fdb761df0e050b0929b93312fc9084bc345726c816952ed0fd4844be27`
- Reuse SHA-256: `27cc27761aaf05e21c9bd91d18e6033630fdae17343b304b745dab7e47d73e34`

Hash-verified prior interpretation:

This theorem proves that 0 is a valid Fin index below n+1 when the implementation has established n=0.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Semantic SHA-256: `56d4f4744c0103a83d3305dc49473baf5a72c1037bbec52ff87f6f4a5419f79e`
- Reuse SHA-256: `d942d9cc459ff4bf7d8639effe97493f97cd3f9742eed184ac611bc79bad45ed`

Hash-verified prior interpretation:

This eliminator splits a Fin-indexed vector according to whether its dimension is zero or a successor.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `d10fc41d6a0da4d7312b4d57df805c426a1be8f3c71cc6f2580a931222e4704b`

Hash-verified prior interpretation:

This projection obtains ordinary division from the real DivInvMonoid instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `f833eed03b65dfa113a80221967b093f8af635c74508930591630ab4499abb29`

Hash-verified prior interpretation:

Fin n is the type of natural indices 0 through n-1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `e08eaa12b36ded072ee70fb1c6bb2c6267f052319ba9b234347ab27535af65cf`

Hash-verified prior interpretation:

This projection invokes the selected heterogeneous addition operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `a56e9de8832095d15b3b690b40013116b0a92d188310b473e03d01d0cbcf12f0`

Hash-verified prior interpretation:

This projection invokes the selected heterogeneous division operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `4e00447a4a8ef4c2ce13e307c56a1fbcd7fa8c732fe039a452b42477a50df2c6`
- Reuse SHA-256: `d685321038674ff25d780889d8ae40d402e73aec05ba894529d34be24cccf43f`

Hash-verified prior interpretation:

This projection invokes the selected heterogeneous multiplication operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `7557f4de6e0cc4b6aec118b769a1c05c84489a818e5b1897c5bc7aaf7849137a`

Hash-verified prior interpretation:

This projection invokes the selected subtraction operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `45854a8d594c50203aa1a44329a98dbb6aeef2ce40e552d48afcc303569f17ec`

Hash-verified prior interpretation:

This projection is the non-strict order relation supplied by a type's LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `fd5699899f1a49c91982cb363d3a71557ab1b53ee772cd777c9ee7717abc2009`
- Reuse SHA-256: `09c7c6f968ffae89af48d2bd684254efac1d8fda7cc01b2228e783b0f301eb71`

Hash-verified prior interpretation:

This projection invokes the selected strict-order relation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `0d849bb90af9029ba46573301a6e413f7cdce60d846545a5aee220a5bb782e47`

Hash-verified prior interpretation:

Nat is the type of nonnegative natural numbers, including zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `da7052ab80d54f5bb3bdaacd7703560baf648ca1316fed1691853c8993fe25aa`

Hash-verified prior interpretation:

This projection interprets numeric literals such as 0 and 1 in the selected type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`
- Reuse SHA-256: `204588d71772f6dd7630088071d44034799a20dfc32327da6658489e77c6779a`

Hash-verified prior interpretation:

This adapter interprets the literal 1 using a type's One instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `ec21591c72e0d59a9b07d790dcc03264434defe02188ba4acb464299be4c972a`

Hash-verified prior interpretation:

Real is mathlib's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Real.exp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Exponential`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `69806b1af98b09fabed435ccc47a9f2f0840f9c5c140fb62cccc81a80761a984`

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
fun x => (Complex.exp (Complex.ofReal x)).re
```

### D028: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `1eeda093709359070c36c2226128b8a9b976290093e2ff13ccd04462ae0732ff`

Hash-verified prior interpretation:

This instance supplies ordinary exact addition of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `e38c1e96a88e4a3352172d2e7917539f965e556f9b5ca045bc83040b9d4b9461`

Hash-verified prior interpretation:

This instance supplies real addition, zero, and additive inverses.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `6d746f2875fc21bd03ae23a424725e4404a4460a28a75da800f82a4084e46192`

Hash-verified prior interpretation:

This instance supplies real multiplication, inversion, and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `2f99677368639b79197e883fdac3e26fa49eb67a383ef2489d3b1bf19540b53b`

Hash-verified prior interpretation:

This is the standard non-strict order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `573bcfac2b62a55b90ee93bf35473d500cc64581698a699b2152c52f40d0e14a`
- Reuse SHA-256: `af54c7b48cdf12b35e73f84db7de83167a1b84a8b5ab01d211271b3d144e61ec`

Hash-verified prior interpretation:

This is the standard strict order on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `8a6b8a7be25e137fac6cfcdd5919f3a6abff4d4677b2211807c6197d5a78456a`

Hash-verified prior interpretation:

This instance supplies ordinary exact multiplication of real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`
- Reuse SHA-256: `ed57860d66650f3ebb09c0ece2c84683256beb7c82b1d93f8d0e9a241eaf3d03`

Hash-verified prior interpretation:

This instance supplies the real multiplicative identity 1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D035: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `c712703cb2f4163d93f7354190ac741e3e3a9fe9372a263bd1427988593d8c0b`

Hash-verified prior interpretation:

Real subtraction is defined as addition of the additive inverse.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D036: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `860eaaa75b06ac6fccbf4f27e9e162807e8851d04bb42d2411332c6368b14882`
- Reuse SHA-256: `528db037cf6bb703fa6fbe98e8eec2ae392126ab646d076ca9f0992c91ce8b23`

Hash-verified prior interpretation:

This instance supplies the real number zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D037: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `2b77f90121aabb95be86d03ed0fa455581a0e363bd58c89de9723fb548c216a2`

Hash-verified prior interpretation:

This instance supplies min and max operations for the standard real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D038: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `f7ebe8a983de002c1ee751fd3c144a7c1933b3bb95c87c5001a3cabf5709031a`
- Reuse SHA-256: `ec0b4bab6097b98eca36b58203587ce19f1d58c697e3c917f52960b9bd254894`

Hash-verified prior interpretation:

This adapter interprets the literal 0 using a type's Zero instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D039: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `9f2383d9e00a51122043cbc3a603fe079c422ea2cd641144cf373a431f839c9c`

Hash-verified prior interpretation:

For reals, abs a is max(a,-a), the standard scalar absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D040: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `0122c17fd89792e177590757e374d925b79be902c03c0b0c4e18f331b083f1de`

Hash-verified prior interpretation:

This adapter turns homogeneous Add into homogeneous HAdd.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D041: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `88680b9843aa138caa8b3352ee05f98af532e3c9fb6f2ed05c25ff1d81d1cb1c`

Hash-verified prior interpretation:

This adapter turns homogeneous Div into homogeneous HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D042: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `b2c5199ab4e68a7588254e144742f0842a3635d412535dc553ae41536cd6fd18`

Hash-verified prior interpretation:

This adapter turns homogeneous Mul into homogeneous HMul.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D043: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `4fd969f28d81771a793607f477bd1aed61c5100b8462a584beff9d68fb7f3976`

Hash-verified prior interpretation:

This adapter turns homogeneous Sub into homogeneous HSub.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D044: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`
- Reuse SHA-256: `ee2dd89dfc929ba345e675f1546305c32e8ffbd5d48c5669ebff22d2c28bb662`

Hash-verified prior interpretation:

Nat.cast maps a natural number to the corresponding value in a type with NatCast.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D045: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`
- Reuse SHA-256: `4543f655bf03d7274acb04e3e31747a0df6831ee2dad918fcceb025b903d8ee8`

Hash-verified prior interpretation:

This instance embeds each natural number as the corresponding real number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D046: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`
- Reuse SHA-256: `24edb147e109a0dff877303ad1184aea3be0367245d532eae881829f302df1b8`

Hash-verified prior interpretation:

And packages simultaneous proofs of two propositions.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D047: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `a9f337b4f0f615f8c81c9a0d21026425f78e7f96b580f4311ede47e8c4fbe3dd`

Hash-verified prior interpretation:

Eq is propositional equality.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D048: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`
- Reuse SHA-256: `417083907f1757c9f6033ee64e7d70768ef160101ff55e55f751d9f52eed9de7`

Hash-verified prior interpretation:

Exists quantifies a witness whose value may depend on preceding universally quantified operands.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D049: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`
- Reuse SHA-256: `6a5b3cbf1d488377ef2edbd9bb48f1cc7e738f175dbd8cb812b620a3fb9d770f`

Hash-verified prior interpretation:

Fin.castSucc embeds an index of a prefix into the successor-sized index type without changing its numeric value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D050: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `664c932a356e9873a3164c26bf0ff18c1d0edb1be4740722e6a9855db9ebc656`

Hash-verified prior interpretation:

This instance enumerates all elements of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D051: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`
- Reuse SHA-256: `0d27b71866609a8aab8de5d5f25f8cfcd53663f8d36346b880d3bca7aae68834`

Hash-verified prior interpretation:

Fin.last n is the final zero-based index n of Fin(n+1).

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D052: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`
- Reuse SHA-256: `56485996bd171b4104d03892f2a47f3021a8bba5e2b294025dd5c2285b40602c`

Hash-verified prior interpretation:

Fin.mk constructs a bounded natural index from its value and proof of its bound.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D053: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `a76fee3ff20746f43f457c001a12b03c42f0845a861d55a233effdf4fc66f51d`

Hash-verified prior interpretation:

Finset.sum maps the indexed terms into the real additive commutative monoid and forms their exact mathematical sum.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D054: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `2bfe1ff78a660dde8a87be42da6310385753d9af95f30d430b0054cb896d4399`

Hash-verified prior interpretation:

Finset.univ is the finite set containing every index of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D055: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`
- Reuse SHA-256: `e8596845d395e77e7a74db75008f7d79bc1b75f760a9a92901aea8d542937a1b`

Hash-verified prior interpretation:

Nat.below packages all smaller recursive results for course-of-values recursion.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D056: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`
- Reuse SHA-256: `aad24107bd8ed08820ac7d83423bbafb44c88b28782f8cbd6bf85f0239ece2c8`

Hash-verified prior interpretation:

Nat.brecOn performs course-of-values recursion on a natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D057: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`
- Reuse SHA-256: `90046ef7cfeac9d4f8eb201b378442b279f01f63463ff927bdf3e0a3c106dd6a`

Hash-verified prior interpretation:

Nat.succ maps n to n+1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D058: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`
- Reuse SHA-256: `388d450d3997e5e56c6ef764726df5fda16c36b97a98c3bfc1f2236ff23b6565`

Hash-verified prior interpretation:

Not P means P implies False.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D059: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `66ed29605d482311b0f4287c2dd239fd34d18ffdca50d9c831bd4666f50300d1`

Hash-verified prior interpretation:

This instance supplies exact associative and commutative real addition with zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D060: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `a2551097d29bac847f3c59e8213b5882afd4a95e9247c2382e8bce33011974b5`
- Reuse SHA-256: `6b0a2a15c9cfb20c266643f0671a950f528e35953cd0cd3660eec092bc1483b4`

Hash-verified prior interpretation:

dite selects a branch based on a decidable proposition and exposes the branch proof.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D061: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`
- Reuse SHA-256: `f4652172d0dddd2d618936f16f311a7079231c0bc7c0a2937114586010003f65`

Hash-verified prior interpretation:

This instance supplies ordinary natural-number addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D062: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`
- Reuse SHA-256: `4139f3f75707c5cc76163d263d1d0b93c35e0a8c98aa5363bfac9c33ce2557f1`

Hash-verified prior interpretation:

This instance decides equality of natural numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D063: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `23a67ca2114d54329d86c3fbe9611953846bde8733017473440dc696933b3861`

Hash-verified prior interpretation:

This instance interprets a natural-number literal as that same natural number.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D064: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`
- Reuse SHA-256: `5193d9fe8084b16f6b4533b0a615298d52247134b2c2de65fb8fd1a899ba9016`

Hash-verified prior interpretation:

Nat.casesOn eliminates a natural number into zero and successor cases.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D065: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`
- Reuse SHA-256: `c44a73c971b14da3ee546fea44ba1254145846a481b1951047fd56f96cdcdad4`

Hash-verified prior interpretation:

Nat.zero is the natural number zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D066: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`
- Reuse SHA-256: `64ee0cd96a16c0da6f12aee7ab9b24d0bcb51006116b4bf91ed3a59435e2ff61`

Hash-verified prior interpretation:

This instance supplies the standard strict order on natural numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
