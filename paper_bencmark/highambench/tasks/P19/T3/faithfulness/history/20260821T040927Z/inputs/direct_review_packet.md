# Declaration dossier for P19-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p19_t3_right_flexible_envelope_comparison {n : ℕ}
    (ug um ua etaR rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ)
    (hum : 0 ≤ um) (hetaR : 0 ≤ etaR) :
    p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv ≤
        p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv ∧
      p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv =
        p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv +
          um * etaR * p19Kappa2 MR MRinv ∧
      (p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv =
          p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv ↔
        um = 0 ∨ etaR = 0 ∨ p19Kappa2 MR MRinv = 0) ∧
      (0 < um → 0 < etaR → 0 < p19Kappa2 MR MRinv →
        p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv <
          p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv)
```

## Elaborated target type

```lean
∀ {n : Nat} (ug um ua etaR rhoA : Real) (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → Real),
  Real.instLE.le 0 um →
    Real.instLE.le 0 etaR →
      And
        (Real.instLE.le (HighamBench.p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
          (HighamBench.p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))
        (And
          (Eq (HighamBench.p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv)
            (instHAdd.hAdd (HighamBench.p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
              (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19Kappa2 MR MRinv))))
          (And
            (Iff
              (Eq (HighamBench.p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
                (HighamBench.p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))
              (Or (Eq um 0) (Or (Eq etaR 0) (Eq (HighamBench.p19Kappa2 MR MRinv) 0))))
            (Real.instLT.lt 0 um →
              Real.instLT.lt 0 etaR →
                Real.instLT.lt 0 (HighamBench.p19Kappa2 MR MRinv) →
                  Real.instLT.lt (HighamBench.p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
                    (HighamBench.p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (ug um ua etaR rhoA : Real) (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → Real)
  (hum : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) um)
  (hetaR :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) etaR),
  And
    (@LE.le.{0} Real Real.instLE (@HighamBench.p19FlexibleEnvelope n ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
      (@HighamBench.p19RightEnvelope n ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))
    (And
      (@Eq.{1} Real (@HighamBench.p19RightEnvelope n ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HighamBench.p19FlexibleEnvelope n ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) um etaR)
            (@HighamBench.p19Kappa2 n MR MRinv))))
      (And
        (Iff
          (@Eq.{1} Real (@HighamBench.p19FlexibleEnvelope n ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
            (@HighamBench.p19RightEnvelope n ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))
          (Or (@Eq.{1} Real um (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
            (Or (@Eq.{1} Real etaR (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
              (@Eq.{1} Real (@HighamBench.p19Kappa2 n MR MRinv)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) um →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) etaR →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@HighamBench.p19Kappa2 n MR MRinv) →
              @LT.lt.{0} Real Real.instLT
                (@HighamBench.p19FlexibleEnvelope n ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv)
                (@HighamBench.p19RightEnvelope n ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P19Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P19Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.CStarAlgebra.Matrix`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p19FlexibleEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2226c7e31f65105121f52189c160e3ef121708a4b6e7b7bfb5d5fb347c4ca505`

Type:

```lean
{n : Nat} →
  Real →
    Real →
      Real →
        (Fin n → Fin n → Real) →
          (Fin n → Fin n → Real) →
            (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (ug ua rhoA : Real) → (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv =>
  instHAdd.hAdd
    (instHMul.hMul (instHMul.hMul ug (HighamBench.p19Kappa2 AMRinv AMRinvInv)) (HighamBench.p19Kappa2 MR MRinv))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19Kappa2 A Ainv)) rhoA)
```

### D002: `HighamBench.p19Kappa2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `b9e5fd26e72448c1ee9298822e9b5726faff2cf4d27bb54e9c9330a2aa739b35`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (A Ainv : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A Ainv => instHMul.hMul (HighamBench.p19OpNorm2 A) (HighamBench.p19OpNorm2 Ainv)
```

### D003: `HighamBench.p19RightEnvelope`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `44a25535cbf646f234b3bc4a2bc4260213f1c22437fd7206200d72d82380ae7e`

Type:

```lean
{n : Nat} →
  Real →
    Real →
      Real →
        Real →
          Real →
            (Fin n → Fin n → Real) →
              (Fin n → Fin n → Real) →
                (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (ug um ua etaR rhoA : Real) → (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv =>
  instHAdd.hAdd
    (instHAdd.hAdd
      (instHMul.hMul (instHMul.hMul ug (HighamBench.p19Kappa2 AMRinv AMRinvInv)) (HighamBench.p19Kappa2 MR MRinv))
      (instHMul.hMul (instHMul.hMul um etaR) (HighamBench.p19Kappa2 MR MRinv)))
    (instHMul.hMul (instHMul.hMul ua (HighamBench.p19Kappa2 A Ainv)) rhoA)
```

### D004: `HighamBench.p19OpNorm2`

- Role: `local`
- Owner module: `HighamBench.P19Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `32c1a2b57edb3d01327a9830854f615bd5cdaf06ad34d12929712c0b11ac6fc8`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.instL2OpNormedAddCommGroup.norm A
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

### D007: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`
- Reuse SHA-256: `012cb4c09296cda2d2b719f4985dbc0a11be1509d6ee40d26e35dcf294e8836e`

Hash-verified prior interpretation:

Fin n is the finite type of natural indices strictly below n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D008: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `e0bf2a92addd6ea713343e4ef69f67e4e1155781d08f46957b9f71412d865f59`
- Reuse SHA-256: `7bc69b64c45ef63c0bf6f48fe61dcfeb042b100678d2dff2765d90c13ddcdec1`

Hash-verified prior interpretation:

Projection of heterogeneous addition from the selected HAdd instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D009: `HMul.hMul`

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

### D010: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D011: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `54a32f2661f788eb2b860006c4d1e8031e126febafe1c8d03ce50529b773dc48`
- Reuse SHA-256: `015523018340c026a6d6478d6d9dd768e7e6f18d5a84f2955ce0c4e73cfc3753`

Hash-verified prior interpretation:

Projection of the binary less-than-or-equal relation from an LE instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D012: `LT.lt`

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

### D013: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Semantic SHA-256: `2e1c25ca42e1e377a41827f0d2f09ae02cfb28ab155c30e277f1000f5e79b32c`
- Reuse SHA-256: `d7c8470c709a528daa626ea536a4c305a0f55c913c79a3c9247a337e503474c2`

Hash-verified prior interpretation:

The natural-number type, including zero.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D014: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Semantic SHA-256: `6a6a0720d091cfeb582747fe67b977e948f09706c0beae1f2f21830aa5821ead`
- Reuse SHA-256: `aa002abdfb6b6111ce60315ea786fba756ac83c928babd7cd98f1862dae1b420`

Hash-verified prior interpretation:

Projection interpreting a numeric literal in a type with an OfNat instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D015: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D016: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`
- Reuse SHA-256: `06e65360d3e77fdde32d1b45c7ac0c74dbef89732b9437af5effe10a33cf292d`

Hash-verified prior interpretation:

Mathlib's exact real-number type.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D017: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `f99208c181266311bec9c890b688378f329076f9e6be38fe93d9cedf4d7f50ce`
- Reuse SHA-256: `fb910383674d6aa41258cec5ed260c8d083be2a0491c4346e4fded114bc95540`

Hash-verified prior interpretation:

The ordinary additive operation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D018: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `144d825fc543455e17044e843560e0415f8e4e9da60afb52f34edb809b7c34d3`
- Reuse SHA-256: `6eada6dc8e6f54bf851e9d68dc2f87b2be3d22403ea011e1cbaa417c7d45a0d9`

Hash-verified prior interpretation:

The ordinary order relation on real numbers.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D019: `Real.instLT`

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

### D020: `Real.instMul`

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
- Semantic SHA-256: `38066efd17aeeca52ec2890d9aafca2fa3cce8fda7f5843c1b8e5da130d93981`
- Reuse SHA-256: `000c506fa5d7241283852e7fb942d058f19bfdd130e97f4af46525062e434105`

Hash-verified prior interpretation:

Builds homogeneous HAdd from an Add instance.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D024: `instHMul`

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

### D025: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`
- Reuse SHA-256: `cb25fd9e6ef05eeebed955028e958dd2b2bd04eb2e1f74710f37029067bb973a`

Hash-verified prior interpretation:

The canonical finite enumeration of Fin n.

Reuse covers declaration meaning only. Re-evaluate this dependency's effect on the current target and its match to the current paper result.

### D026: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e552ffc8c85b917dca38e5965ad91773fdb989246623a528d91526b75d68c2f1`

Type:

```lean
Type u → Type u' → Type v → Type (max u u' v)
```

Fully explicit type:

```lean
(m : Type u) → (n : Type u') → (α : Type v) → Type (max u u' v)
```

Definition body (one-level semantic boundary):

```lean
fun m n α => m → n → α
```

### D027: `Matrix.instL2OpNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.CStarAlgebra.Matrix`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `dc6ff9e1f662ed3b176ef586f3e0ff253c161538742e908216485822af6e00c3`

Type:

```lean
{𝕜 : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} → [RCLike 𝕜] → [Fintype m] → [Fintype n] → [DecidableEq n] → NormedAddCommGroup (Matrix m n 𝕜)
```

Fully explicit type:

```lean
{𝕜 : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      [RCLike.{u_1} 𝕜] →
        [Fintype.{u_2} m] →
          [Fintype.{u_3} n] →
            [DecidableEq.{u_3 + 1} n] → NormedAddCommGroup.{max (max u_1 u_3) u_2} (Matrix.{u_2, u_3, u_1} m n 𝕜)
```

Definition body (one-level semantic boundary):

```lean
fun {𝕜} {m} {n} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n] =>
  { toNorm := Matrix.l2OpNormedAddCommGroupAux.toNorm, toAddCommGroup := Matrix.addCommGroup,
    toMetricSpace := Matrix.instL2OpMetricSpace, dist_eq := ⋯ }
```

### D028: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Fully explicit type:

```lean
{E : Type u_8} → [self : Norm.{u_8} E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D029: `NormedAddCommGroup.toNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `702f98e978ba8cf9fe1b4ce130f011682d6d486d71ba0f7d12f36ec9925cd59b`

Type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup E] → Norm E
```

Fully explicit type:

```lean
{E : Type u_8} → [self : NormedAddCommGroup.{u_8} E] → Norm.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [self : NormedAddCommGroup E] => self.1
```

### D030: `Real.instRCLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.RCLike.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d2fdb97b9d861fcf61e6dbea9993dfa0ca6aa16609742f215c35b3f7ddd16b8e`

Type:

```lean
RCLike Real
```

Fully explicit type:

```lean
RCLike.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toDenselyNormedField := Real.denselyNormedField, toStarRing := instStarRingReal,
  toNormedAlgebra := NormedAlgebra.id Real, toCompleteSpace := Real.instCompleteSpace, re := AddMonoidHom.id Real,
  im := 0, I := 0, I_re_ax := Real.instRCLike._proof_1, I_mul_I_ax := Real.instRCLike._proof_8, re_add_im_ax := ⋯,
  ofReal_re_ax := Real.instRCLike._proof_11, ofReal_im_ax := Real.instRCLike._proof_12, mul_re_ax := ⋯, mul_im_ax := ⋯,
  conj_re_ax := ⋯, conj_im_ax := ⋯, conj_I_ax := Real.instRCLike._proof_7, norm_sq_eq_def_ax := ⋯, mul_im_I_ax := ⋯,
  toPartialOrder := Real.partialOrder, le_iff_re_im := @Real.instRCLike._proof_13, toDecidableEq := Real.decidableEq }
```

### D031: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → DecidableEq.{1} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```
