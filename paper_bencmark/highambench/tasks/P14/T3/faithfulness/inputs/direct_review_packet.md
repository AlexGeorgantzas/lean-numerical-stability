# Declaration dossier for P14-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p14_t3_softmax_shift_and_normalization {n : ℕ}
    (x : Fin n → ℝ) (a : ℝ) (j : Fin n) :
    p14Softmax (fun i => x i - a) j = p14Softmax x j ∧
      (∑ i, p14Softmax x i) = 1 ∧
      (∑ i, |p14Softmax x i|) = 1
```

## Elaborated target type

```lean
∀ {n : Nat} (x : Fin n → Real) (a : Real) (j : Fin n),
  And (Eq (HighamBench.p14Softmax (fun i => instHSub.hSub (x i) a) j) (HighamBench.p14Softmax x j))
    (And (Eq (Finset.univ.sum fun i => HighamBench.p14Softmax x i) 1)
      (Eq (Finset.univ.sum fun i => abs (HighamBench.p14Softmax x i)) 1))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (x : Fin n → Real) (a : Real) (j : Fin n),
  And
    (@Eq.{1} Real
      (@HighamBench.p14Softmax n
        (fun (i : Fin n) => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (x i) a) j)
      (@HighamBench.p14Softmax n x j))
    (And
      (@Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n))
          fun (i : Fin n) => @HighamBench.p14Softmax n x i)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@Eq.{1} Real
        (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n))
          fun (i : Fin n) => @abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p14Softmax n x i))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P14Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P14Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p14Softmax`

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

### D002: `HighamBench.p14ExpSum`

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

### D003: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`
- Reuse SHA-256: `24edb147e109a0dff877303ad1184aea3be0367245d532eae881829f302df1b8`

Hash-verified prior interpretation:

And packages simultaneous proofs of two propositions.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`
- Reuse SHA-256: `a9f337b4f0f615f8c81c9a0d21026425f78e7f96b580f4311ede47e8c4fbe3dd`

Hash-verified prior interpretation:

Eq is propositional equality.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `f833eed03b65dfa113a80221967b093f8af635c74508930591630ab4499abb29`

Hash-verified prior interpretation:

Fin n is the type of natural indices 0 through n-1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D006: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `664c932a356e9873a3164c26bf0ff18c1d0edb1be4740722e6a9855db9ebc656`

Hash-verified prior interpretation:

This instance enumerates all elements of Fin n exactly once.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `a76fee3ff20746f43f457c001a12b03c42f0845a861d55a233effdf4fc66f51d`

Hash-verified prior interpretation:

Finset.sum maps the indexed terms into the real additive commutative monoid and forms their exact mathematical sum.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `2bfe1ff78a660dde8a87be42da6310385753d9af95f30d430b0054cb896d4399`

Hash-verified prior interpretation:

Finset.univ is the finite set containing every index of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`
- Reuse SHA-256: `7557f4de6e0cc4b6aec118b769a1c05c84489a818e5b1897c5bc7aaf7849137a`

Hash-verified prior interpretation:

This projection invokes the selected subtraction operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `0d849bb90af9029ba46573301a6e413f7cdce60d846545a5aee220a5bb782e47`

Hash-verified prior interpretation:

Nat is the type of nonnegative natural numbers, including zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `da7052ab80d54f5bb3bdaacd7703560baf648ca1316fed1691853c8993fe25aa`

Hash-verified prior interpretation:

This projection interprets numeric literals such as 0 and 1 in the selected type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Semantic SHA-256: `cc544b5b2a2aabc84389a9fe2f052127dc6dae9964782b117b9b19b773e542d5`
- Reuse SHA-256: `204588d71772f6dd7630088071d44034799a20dfc32327da6658489e77c6779a`

Hash-verified prior interpretation:

This adapter interprets the literal 1 using a type's One instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `ec21591c72e0d59a9b07d790dcc03264434defe02188ba4acb464299be4c972a`

Hash-verified prior interpretation:

Real is mathlib's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `66ed29605d482311b0f4287c2dd239fd34d18ffdca50d9c831bd4666f50300d1`

Hash-verified prior interpretation:

This instance supplies exact associative and commutative real addition with zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f0de8cbc2c873a19be749cd9b2d3cc9a6edb9ebc92020a1877714a50c23d9dc0`
- Reuse SHA-256: `e38c1e96a88e4a3352172d2e7917539f965e556f9b5ca045bc83040b9d4b9461`

Hash-verified prior interpretation:

This instance supplies real addition, zero, and additive inverses.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `b4e24b050b7fb50c4c115c51d5cd4c1b180cae53633f58a38c7d5ce3ccf86c81`
- Reuse SHA-256: `ed57860d66650f3ebb09c0ece2c84683256beb7c82b1d93f8d0e9a241eaf3d03`

Hash-verified prior interpretation:

This instance supplies the real multiplicative identity 1.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`
- Reuse SHA-256: `c712703cb2f4163d93f7354190ac741e3e3a9fe9372a263bd1427988593d8c0b`

Hash-verified prior interpretation:

Real subtraction is defined as addition of the additive inverse.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `5bccf78d647cf08233ff548c19523f80b1d1bf11b5a76aa50396199e2c0c7510`
- Reuse SHA-256: `2b77f90121aabb95be86d03ed0fa455581a0e363bd58c89de9723fb548c216a2`

Hash-verified prior interpretation:

This instance supplies min and max operations for the standard real order.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Semantic SHA-256: `8ec55bade8dee4d49822a9bdbd84db24c019b8d568452329d9766390229a9c1b`
- Reuse SHA-256: `9f2383d9e00a51122043cbc3a603fe079c422ea2cd641144cf373a431f839c9c`

Hash-verified prior interpretation:

For reals, abs a is max(a,-a), the standard scalar absolute value.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`
- Reuse SHA-256: `4fd969f28d81771a793607f477bd1aed61c5100b8462a584beff9d68fb7f3976`

Hash-verified prior interpretation:

This adapter turns homogeneous Sub into homogeneous HSub.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `cf21e4a4c962ee0db8a97bd649d849a798a693692bf09312f7855ddcbeb125ea`
- Reuse SHA-256: `d10fc41d6a0da4d7312b4d57df805c426a1be8f3c71cc6f2580a931222e4704b`

Hash-verified prior interpretation:

This projection obtains ordinary division from the real DivInvMonoid instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D022: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `10d75d9f08ad8c923109392866fba5fb3645de144bc824cefdd353658fe9f06b`
- Reuse SHA-256: `a56e9de8832095d15b3b690b40013116b0a92d188310b473e03d01d0cbcf12f0`

Hash-verified prior interpretation:

This projection invokes the selected heterogeneous division operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Real.exp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Exponential`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D024: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `166f2abb65bf1271e5e8d70fdb78c55672c7e366b30439e83b517f803cdefac3`
- Reuse SHA-256: `6d746f2875fc21bd03ae23a424725e4404a4460a28a75da800f82a4084e46192`

Hash-verified prior interpretation:

This instance supplies real multiplication, inversion, and division.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `ea3478ce3daf37e2cbdcd4bfaf7b5142fd7d274b56d75d2fae007c15e1b89871`
- Reuse SHA-256: `88680b9843aa138caa8b3352ee05f98af532e3c9fb6f2ed05c25ff1d81d1cb1c`

Hash-verified prior interpretation:

This adapter turns homogeneous Div into homogeneous HDiv.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
