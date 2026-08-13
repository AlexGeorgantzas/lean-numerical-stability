# Declaration dossier for P15-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p15_t2_low_rank_matvec_backward_error {n : ℕ}
    (A Atilde truncError roundingError : P15Matrix n)
    (v computed : P15Vector n) (epsilon beta gammaC : ℝ)
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 ≤ beta) (hgammaC : 0 ≤ gammaC)
    (happrox : Atilde = A + truncError)
    (hcomputed : computed = p15MatVec (Atilde + roundingError) v)
    (htrunc : p15FrobNorm truncError ≤ epsilon * beta)
    (hround : p15FrobNorm roundingError ≤ gammaC * p15FrobNorm Atilde) :
    ∃ totalError : P15Matrix n,
      computed = p15MatVec (A + totalError) v ∧
      p15FrobNorm totalError ≤
        gammaC * p15FrobNorm A + epsilon * (1 + gammaC) * beta
```

## Elaborated target type

```lean
∀ {n : Nat} (A Atilde truncError roundingError : HighamBench.P15Matrix n) (v computed : HighamBench.P15Vector n)
  (epsilon beta gammaC : Real),
  Real.instLE.le 0 epsilon →
    Real.instLE.le 0 beta →
      Real.instLE.le 0 gammaC →
        Eq Atilde (instHAdd.hAdd A truncError) →
          Eq computed (HighamBench.p15MatVec (instHAdd.hAdd Atilde roundingError) v) →
            Real.instLE.le (HighamBench.p15FrobNorm truncError) (instHMul.hMul epsilon beta) →
              Real.instLE.le (HighamBench.p15FrobNorm roundingError)
                  (instHMul.hMul gammaC (HighamBench.p15FrobNorm Atilde)) →
                Exists fun totalError =>
                  And (Eq computed (HighamBench.p15MatVec (instHAdd.hAdd A totalError) v))
                    (Real.instLE.le (HighamBench.p15FrobNorm totalError)
                      (instHAdd.hAdd (instHMul.hMul gammaC (HighamBench.p15FrobNorm A))
                        (instHMul.hMul (instHMul.hMul epsilon (instHAdd.hAdd 1 gammaC)) beta)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A Atilde truncError roundingError : HighamBench.P15Matrix n) (v computed : HighamBench.P15Vector n)
  (epsilon beta gammaC : Real)
  (hepsilon :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon)
  (hbeta : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) beta)
  (hgammaC :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) gammaC)
  (happrox :
    @Eq.{1} (HighamBench.P15Matrix n) Atilde
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
        (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) A
        truncError))
  (hcomputed :
    @Eq.{1} (HighamBench.P15Vector n) computed
      (@HighamBench.p15MatVec n
        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
          (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) Atilde
          roundingError)
        v))
  (htrunc :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n truncError)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon beta))
  (hround :
    @LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n roundingError)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC
        (@HighamBench.p15FrobNorm n Atilde))),
  @Exists.{1} (HighamBench.P15Matrix n) fun (totalError : HighamBench.P15Matrix n) =>
    And
      (@Eq.{1} (HighamBench.P15Vector n) computed
        (@HighamBench.p15MatVec n
          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P15Matrix n) (HighamBench.P15Matrix n) (HighamBench.P15Matrix n)
            (@instHAdd.{0} (HighamBench.P15Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) A
            totalError)
          v))
      (@LE.le.{0} Real Real.instLE (@HighamBench.p15FrobNorm n totalError)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gammaC (@HighamBench.p15FrobNorm n A))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) gammaC))
            beta)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P15Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P15Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P15Matrix`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `869888198c7e16028812ecb8af419ae2eacf78a03074fe8308f98d5758ed7656`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Matrix (Fin n) (Fin n) Real
```

### D002: `HighamBench.P15Vector`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `15e7e37c5731d7df61fbacb22e39e6f80678f5f9880fecbb579e57644d05505c`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

Definition body (one-level semantic boundary):

```lean
fun n => Fin n → Real
```

### D003: `HighamBench.p15FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Semantic SHA-256: `ba1b58b4e7fdbcda54fe1a9ee4d2ebd9f8d43b80907403bf6ea885fff386083f`
- Reuse SHA-256: `6a91bf9c84bfcbacb1ea3b560b005b8de47822ea8755913ca95adfd0a9e1869d`

Hash-verified prior interpretation:

The function returns the norm field of Matrix.frobeniusNormedRing for the supplied finite square real matrix.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D004: `HighamBench.p15MatVec`

- Role: `local`
- Owner module: `HighamBench.P15Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `46653426fb5f80e06b04a77772652321fa618edf797127f16a95ad856ba2a7a8`

Type:

```lean
{n : Nat} → HighamBench.P15Matrix n → HighamBench.P15Vector n → HighamBench.P15Vector n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P15Matrix n) → (x : HighamBench.P15Vector n) → HighamBench.P15Vector n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D005: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D006: `Eq`

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

### D007: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `a24a6eb72dcf5b3765659a28bb9d3814ed7ebd3e3fa1fd11e8f3c7acc80e0dde`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D008: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `e737486c67f9dbea0f2bcbe83634be51e58d0d92cf1cfb23c776a2f4a7e59c97`

Hash-verified prior interpretation:

Fin n is the finite bounded index type with n elements.

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
- Reuse SHA-256: `3572f804982d8e02cdb90fefa4ba09c86e248bb74e338dbccdf5e34e05538eb1`

Hash-verified prior interpretation:

This abbreviation selects the binary multiplication operation from an HMul instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D011: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `ba63226d47485a0686b361b82ac9938d26080ba88527d42eda0b433bc8a394af`

Hash-verified prior interpretation:

This abbreviation selects the non-strict order relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add α] → Add (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Add.{v} α] → Add.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Add α] => Pi.instAdd
```

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `ed4370998b8d9dbde5a6b5b4d574c7c396509b78ab3bca72cc8b612c8d4357de`

Hash-verified prior interpretation:

Nat supplies the target's matrix-size parameter n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `OfNat.ofNat`

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

### D015: `One.toOfNat1`

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

### D016: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `33b5a5009512de034973263c33e6107bb25484411cca37b571a00491e1dc8681`

Hash-verified prior interpretation:

Real is the scalar type of every matrix entry and the codomain of the norm.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instAdd`

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

### D018: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `6005e17e5289b370343d36a1373b58f2243742c58aacd4708762ee2b8f8403e7`

Hash-verified prior interpretation:

This instance installs the ordinary real order Real.le as LE Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `459ccbe28a1d29ccd2b329ea29e1a84b329b8064b8a8ecc52764b69b23e229ed`
- Reuse SHA-256: `bc3810a73f8d595e308695fedc5608856bba227a7ac7eb8d39a9aea9023506a9`

Hash-verified prior interpretation:

This instance installs ordinary real multiplication as Mul Real.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D020: `Real.instOne`

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

### D021: `Real.instZero`

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

### D022: `Zero.toOfNat0`

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

### D023: `instHAdd`

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

### D024: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `1fd375514ac68e29e7941c94ba308ea936395db23d0fee63a5c69dcccd3b2bdc`
- Reuse SHA-256: `3b55530701c5ce29596c1bf762341e1b88002ec2ffa277efcd64bb97025789ef`

Hash-verified prior interpretation:

This construction turns a homogeneous Mul instance into an HMul instance by using the same multiplication operation.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D025: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `8457a8d4ad0d78e4cf0c14700f1480df720d518fa77b11738bbce3325090eee5`

Hash-verified prior interpretation:

This instance enumerates all elements of Fin n using finRange n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`
- Reuse SHA-256: `fa5c7c8cb376d6defbad0c4b48ccd19139f66e98f56c7ce2c55d211e8fbea4d6`

Hash-verified prior interpretation:

Finset.sum maps a function over a finite set and combines the results with commutative-monoid addition.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D027: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`
- Reuse SHA-256: `d34f479cade36f2caaaeb813b8e491070246e5aa1c89610ed2939d9020326955`

Hash-verified prior interpretation:

Finset.univ selects all elements supplied by a Fintype instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D028: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`
- Reuse SHA-256: `9f65add277408970718ba49cc0f20472a0d50ce11ba23dfae35afc9b92aa201a`

Hash-verified prior interpretation:

Matrix m n alpha is definitionally the function type m -> n -> alpha.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D029: `Matrix.frobeniusNormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Matrix.Normed`
- Declaration kind: `def`
- Semantic SHA-256: `883d6b4ab1d783b7d3150d110714b2fc1951827b2bacd53b49e46c8b1e7d00a4`
- Reuse SHA-256: `9c4583ea78f575b045680ee6d7f1b24bc850c7fc1e7c142d50ce821c0c823c4f`

Hash-verified prior interpretation:

This instance combines the matrix ring operations with the norm inherited from Matrix.frobeniusSeminormedAddCommGroup and includes Frobenius-norm submultiplicativity.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D030: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`
- Reuse SHA-256: `d85b24047182364c6d653ef7a6dc1b8fbf56132f7c05e7422dff98364ef3b656`

Hash-verified prior interpretation:

This abbreviation projects the norm function from a Norm instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D031: `NormedRing.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Semantic SHA-256: `0957abfc66401a60ac36872f31eb54890d14b0b45613e38ba8f235c467f63751`
- Reuse SHA-256: `7b650485a13ebb4f91630d4a15ff66e9b6446a56cf1c892594741b7c2e7cc33e`

Hash-verified prior interpretation:

This abbreviation projects the Norm structure contained in a NormedRing.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D032: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `11a549e6c9caa007a4627570dd86aea756ada755f141da0356b8766788f2eef7`
- Reuse SHA-256: `9535fc8b7317cb6988393fc4e210d35fb791659d51385e14049518b93614fcee`

Hash-verified prior interpretation:

This instance supplies real zero and commutative addition for finite sums.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D033: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`
- Reuse SHA-256: `6cd230752e597453d6b57a967a53b590162a3a2cf6278ed6e067438550193c58`

Hash-verified prior interpretation:

This instance equips Real with the RCLike structure used by the Frobenius matrix norm construction.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D034: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`
- Reuse SHA-256: `44a573b68a98935896e14a575844e3cd0229658a863bdabc933be0e006f683c0`

Hash-verified prior interpretation:

This instance decides equality of Fin n indices by deciding equality of their underlying natural values.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.
