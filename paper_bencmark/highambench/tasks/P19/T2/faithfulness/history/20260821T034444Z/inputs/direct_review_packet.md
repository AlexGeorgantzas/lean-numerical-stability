# Declaration dossier for P19-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t2_modular_four_source_error_bound {n : ℕ}
    (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ)
    (computationError rhsError gmresError solutionError : Fin n → ℝ)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda)
    (hcomputation : p19VecNorm2 computationError ≤ epsilonC)
    (hrhs : p19VecNorm2 rhsError ≤ epsilonB)
    (hgmres : p19VecNorm2 gmresError ≤ ug)
    (hsolution : p19VecNorm2 solutionError ≤ epsilonX) :
    p19VecNorm2
        (p19ModularError alpha beta lambda computationError rhsError
          gmresError solutionError) ≤
      p19ModularEnvelope alpha beta lambda epsilonC epsilonB ug epsilonX
```

## Elaborated target type

```lean
∀ {n : Nat} (alpha beta lambda epsilonC epsilonB ug epsilonX : Real)
  (computationError rhsError gmresError solutionError : Fin n → Real),
  Real.instLE.le 0 alpha →
    Real.instLE.le 0 beta →
      Real.instLE.le 0 lambda →
        Real.instLE.le (HighamBench.p19VecNorm2 computationError) epsilonC →
          Real.instLE.le (HighamBench.p19VecNorm2 rhsError) epsilonB →
            Real.instLE.le (HighamBench.p19VecNorm2 gmresError) ug →
              Real.instLE.le (HighamBench.p19VecNorm2 solutionError) epsilonX →
                Real.instLE.le
                  (HighamBench.p19VecNorm2
                    (HighamBench.p19ModularError alpha beta lambda computationError rhsError gmresError solutionError))
                  (HighamBench.p19ModularEnvelope alpha beta lambda epsilonC epsilonB ug epsilonX)
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (alpha beta lambda epsilonC epsilonB ug epsilonX : Real)
  (computationError rhsError gmresError solutionError : Fin n → Real)
  (halpha :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) alpha)
  (hbeta : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) beta)
  (hlambda :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) lambda)
  (hcomputation : @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 n computationError) epsilonC)
  (hrhs : @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 n rhsError) epsilonB)
  (hgmres : @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 n gmresError) ug)
  (hsolution : @LE.le.{0} Real Real.instLE (@HighamBench.p19VecNorm2 n solutionError) epsilonX),
  @LE.le.{0} Real Real.instLE
    (@HighamBench.p19VecNorm2 n
      (@HighamBench.p19ModularError n alpha beta lambda computationError rhsError gmresError solutionError))
    (HighamBench.p19ModularEnvelope alpha beta lambda epsilonC epsilonB ug epsilonX)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.CStarAlgebra.Matrix`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p19ModularEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4d1f50569f1e938522ad9eb1ae93404d40243c6ec09407ff5120e6b1032a551c`

Type:

```lean
Real → Real → Real → Real → Real → Real → Real → Real
```

Fully explicit type:

```lean
(alpha beta lambda epsilonC epsilonB ug epsilonX : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun alpha beta lambda epsilonC epsilonB ug epsilonX =>
  instHAdd.hAdd
    (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul alpha epsilonC) (instHMul.hMul beta epsilonB)) (instHMul.hMul beta ug))
    (instHMul.hMul lambda epsilonX)
```

### D002: `HighamBench.p19ModularError`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `92e2cc2e752ab702ab9e8cb2f24d2a42643041e163d091702a5e0dc01d22042f`

Type:

```lean
{n : Nat} → Real → Real → Real → (Fin n → Real) → (Fin n → Real) → (Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (alpha beta lambda : Real) → (computationError rhsError gmresError solutionError : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} alpha beta lambda computationError rhsError gmresError solutionError =>
  HighamBench.p19Add (HighamBench.p19Scale alpha computationError)
    (HighamBench.p19Add (HighamBench.p19Scale beta rhsError)
      (HighamBench.p19Add (HighamBench.p19Scale beta gmresError) (HighamBench.p19Scale lambda solutionError)))
```

### D003: `HighamBench.p19VecNorm2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `6b6e1bd375429f5aeb20a6f7108df37b3e72d1ec77d5e9de9ed7b15b6a12565e`
- Reuse SHA-256: `14a2c612928203ac40e74d2f55e8404ea50451f6984a6421617705f1e7bddacb`

Hash-verified prior interpretation:

The square root of p19VecNorm2Sq, hence the Euclidean norm because the squared quantity is a nonnegative sum of coordinate squares.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p19Add`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `312c3e2303d89086bfc91423334bf696f5e51c2415a0575fd2d077d7c4f7d7d6`
- Reuse SHA-256: `8e0270b08f8021fe85c3a408145727787cf090338a737dc486fa30c04ede5e17`

Hash-verified prior interpretation:

Componentwise addition of two real vectors indexed by Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D005: `HighamBench.p19Scale`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e1c4e4f726820a072f1177bef99a898faaa173c570ae9a33887cd9d2cc517066`

Type:

```lean
{n : Nat} → Real → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (a : Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} a x i => instHMul.hMul a (x i)
```

### D006: `HighamBench.p19VecNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `e29dbb51f77b0df1c2e4cbb308e8a6e36e232c2b0ce38cd883c0b946cd01ea97`
- Reuse SHA-256: `dd145afff528dfa4167f1b6a5a5aa2a64d54b3fb1091dd62674063f9e9a17e45`

Hash-verified prior interpretation:

The finite sum over all coordinates of x_i raised to the natural power 2.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D007: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `012cb4c09296cda2d2b719f4985dbc0a11be1509d6ee40d26e35dcf294e8836e`

Hash-verified prior interpretation:

Fin n is the finite type of natural indices strictly below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `015523018340c026a6d6478d6d9dd768e7e6f18d5a84f2955ce0c4e73cfc3753`

Hash-verified prior interpretation:

Projection of the binary less-than-or-equal relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `d7c8470c709a528daa626ea536a4c305a0f55c913c79a3c9247a337e503474c2`

Hash-verified prior interpretation:

The natural-number type, including zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D010: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `aa002abdfb6b6111ce60315ea786fba756ac83c928babd7cd98f1862dae1b420`

Hash-verified prior interpretation:

Projection interpreting a numeric literal in a type with an OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `06e65360d3e77fdde32d1b45c7ac0c74dbef89732b9437af5effe10a33cf292d`

Hash-verified prior interpretation:

Mathlib's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `6eada6dc8e6f54bf851e9d68dc2f87b2be3d22403ea011e1cbaa417c7d45a0d9`

Hash-verified prior interpretation:

The ordinary order relation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D013: `Real.instZero`

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

### D014: `Zero.toOfNat0`

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

### D015: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `7bc69b64c45ef63c0bf6f48fe61dcfeb042b100678d2dff2765d90c13ddcdec1`

Hash-verified prior interpretation:

Projection of heterogeneous addition from the selected HAdd instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D016: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D017: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `fb910383674d6aa41258cec5ed260c8d083be2a0491c4346e4fded114bc95540`

Hash-verified prior interpretation:

The ordinary additive operation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D019: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Semantic SHA-256: `67f9248ae1acb851b5392be301057ebb8b8ef2fb20f76d2d53a2d07ec8f30553`
- Reuse SHA-256: `37922635c73a13f3a8ad57f14fb6afac4e81543f3c660491922d0dfb107ada72`

Hash-verified prior interpretation:

The nonnegative real square root; its truncating behavior on negative inputs is irrelevant because p19VecNorm2Sq is a sum of squares.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `000c506fa5d7241283852e7fb942d058f19bfdd130e97f4af46525062e434105`

Hash-verified prior interpretation:

Builds homogeneous HAdd from an Add instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D021: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D022: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `cb25fd9e6ef05eeebed955028e958dd2b2bd04eb2e1f74710f37029067bb973a`

Hash-verified prior interpretation:

The canonical finite enumeration of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D023: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `c23b45e8ff4789d8b9652a822d6335e12674b808660163fdf8f8d99668ed2aed`

Hash-verified prior interpretation:

Finite summation in a commutative additive monoid.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `642fd1a8a34ebc5e9684d7d0214c7be0ec03bc1195e08be3a155f3ecc28eefe1`

Hash-verified prior interpretation:

The finite set containing every element of a Fintype.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6196b8cbb884c4f39841ba74b23d75f3c753fe0d044cc402bd6e4e3bd59d5cb8`
- Reuse SHA-256: `1b90923d912c62adb0420e9d0b84327a19b55fcecd77f82924c07a01558440f6`

Hash-verified prior interpretation:

Projection of heterogeneous exponentiation from the selected HPow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`
- Reuse SHA-256: `f6770f45042024e09d6f39cd77dbafa5193a52fb060b2b5ccf76f05d6f49202b`

Hash-verified prior interpretation:

The natural-number power operation induced by the multiplicative monoid structure.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `74dcbafa22ffd84bda5d3114483ee6598e8965b35a9fcbf2c6220893799fa398`

Hash-verified prior interpretation:

The standard commutative additive monoid structure on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`
- Reuse SHA-256: `5a0175da8fbbe5aac5bb7ec9c410c16dba2c5e06023e23ef7ad02c7f222d89ff`

Hash-verified prior interpretation:

The standard multiplicative monoid structure on Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `eb300d353d84392c776cad5e356479f878030744a43f9a1584942a89d16350b4`
- Reuse SHA-256: `6a4765dd98715a3dd1c0399f7ec6ff393d83a4044a98c5577fe424fc1575aa33`

Hash-verified prior interpretation:

Builds HPow from the applicable Pow instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7018dea92aae8c272f3a065f25e2bedb9732a0b602c3d54b166fa0cf2ce1ea92`
- Reuse SHA-256: `f1c070b8b2dec2badd1514b96d23d0f633a797b5dadcd9c441fd739b6ee0b92e`

Hash-verified prior interpretation:

The canonical interpretation of a natural-number literal as itself.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
