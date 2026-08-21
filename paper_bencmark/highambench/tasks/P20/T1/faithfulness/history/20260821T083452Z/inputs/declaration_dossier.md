# Declaration dossier for P20-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p20_t1_power_two_row_scaling {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (fmax Fmax : ℝ)
    (hm : 0 < m) (hn : 0 < n)
    (hfmax : 0 < fmax) (hFmax : 0 < Fmax)
    (hrow : ∀ i : Fin m, 0 < p20InfNormVec (A i)) :
    let theta := p20ScalingThreshold n fmax Fmax
    (∀ i : Fin m,
        p20IsPowerOfTwo (p20RowScaleFactor theta (A i)) ∧
          0 < p20RowScaleFactor theta (A i) ∧
          theta / (2 * p20InfNormVec (A i)) <
            p20RowScaleFactor theta (A i) ∧
          p20RowScaleFactor theta (A i) ≤
            theta / p20InfNormVec (A i)) ∧
      (∀ i : Fin m, ∀ j : Fin n,
        |p20LeftScaledMatrix theta A i j| ≤ theta) ∧
      ∀ i : Fin m, ∃ j : Fin n,
        theta / 2 < |p20LeftScaledMatrix theta A i j|
```

## Elaborated target type

```lean
∀ {m n : Nat} (A : Matrix (Fin m) (Fin n) Real) (fmax Fmax : Real),
  instLTNat.lt 0 m →
    instLTNat.lt 0 n →
      Real.instLT.lt 0 fmax →
        Real.instLT.lt 0 Fmax →
          (∀ (i : Fin m), Real.instLT.lt 0 (HighamBench.p20InfNormVec (A i))) →
            have theta := HighamBench.p20ScalingThreshold n fmax Fmax;
            And
              (∀ (i : Fin m),
                And (HighamBench.p20IsPowerOfTwo (HighamBench.p20RowScaleFactor theta (A i)))
                  (And (Real.instLT.lt 0 (HighamBench.p20RowScaleFactor theta (A i)))
                    (And
                      (Real.instLT.lt (instHDiv.hDiv theta (instHMul.hMul 2 (HighamBench.p20InfNormVec (A i))))
                        (HighamBench.p20RowScaleFactor theta (A i)))
                      (Real.instLE.le (HighamBench.p20RowScaleFactor theta (A i))
                        (instHDiv.hDiv theta (HighamBench.p20InfNormVec (A i)))))))
              (And (∀ (i : Fin m) (j : Fin n), Real.instLE.le (abs (HighamBench.p20LeftScaledMatrix theta A i j)) theta)
                (∀ (i : Fin m),
                  Exists fun j =>
                    Real.instLT.lt (instHDiv.hDiv theta 2) (abs (HighamBench.p20LeftScaledMatrix theta A i j))))
```

## Fully explicit elaborated target type

```lean
∀ {m n : Nat} (A : Matrix.{0, 0, 0} (Fin m) (Fin n) Real) (fmax Fmax : Real)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
  (hfmax : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) fmax)
  (hFmax : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Fmax)
  (hrow :
    ∀ (i : Fin m),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HighamBench.p20InfNormVec n (A i))),
  have theta : Real := HighamBench.p20ScalingThreshold n fmax Fmax;
  And
    (∀ (i : Fin m),
      And (HighamBench.p20IsPowerOfTwo (@HighamBench.p20RowScaleFactor n theta (A i)))
        (And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@HighamBench.p20RowScaleFactor n theta (A i)))
          (And
            (@LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) theta
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@HighamBench.p20InfNormVec n (A i))))
              (@HighamBench.p20RowScaleFactor n theta (A i)))
            (@LE.le.{0} Real Real.instLE (@HighamBench.p20RowScaleFactor n theta (A i))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) theta
                (@HighamBench.p20InfNormVec n (A i)))))))
    (And
      (∀ (i : Fin m) (j : Fin n),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p20LeftScaledMatrix m n theta A i j)) theta)
      (∀ (i : Fin m),
        @Exists.{1} (Fin n) fun (j : Fin n) =>
          @LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) theta
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.p20LeftScaledMatrix m n theta A i j))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P20Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P20Definitions` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Archimedean.Basic`, `Mathlib.Analysis.Asymptotics.Lemmas`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Real.Sqrt`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.p20InfNormVec`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `87f59ddda7d28f2342745750052393a1a7f8e6da20099629ce901b53ae3a06a8`

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
fun {n} x => (Finset.univ.sup fun i => (abs (x i)).toNNReal).toReal
```

### D002: `HighamBench.p20IsPowerOfTwo`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `cdbc02ca950134eb20d94e5488f66c176cc912c7aa24e523ded6bd5ee37e98e5`

Type:

```lean
Real → Prop
```

Fully explicit type:

```lean
(lambda : Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun lambda => Exists fun exponent => Eq lambda (instHPow.hPow 2 exponent)
```

### D003: `HighamBench.p20LeftScaledMatrix`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6f988a6386e7725eb31fb4ad1a30c426185791b6fd0c83740651bd5983ff3375`

Type:

```lean
{m n : Nat} → Real → Matrix (Fin m) (Fin n) Real → Matrix (Fin m) (Fin n) Real
```

Fully explicit type:

```lean
{m n : Nat} → (theta : Real) → (A : Matrix.{0, 0, 0} (Fin m) (Fin n) Real) → Matrix.{0, 0, 0} (Fin m) (Fin n) Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} theta A => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (HighamBench.p20RowScalingMatrix theta A) A
```

### D004: `HighamBench.p20RowScaleFactor`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `77140c233b5d98cb13aecd5a542d75ce873142994d6283281df6171127d0d23d`

Type:

```lean
{n : Nat} → Real → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (theta : Real) → (x : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} theta x => instHPow.hPow 2 (HighamBench.p20RowScaleExponent theta x)
```

### D005: `HighamBench.p20ScalingThreshold`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `9f68c8a231e4cea47898d3834d4362c543f7e7455dc046f54bb660b2dff27910`

Type:

```lean
Nat → Real → Real → Real
```

Fully explicit type:

```lean
(n : Nat) → (fmax Fmax : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n fmax Fmax => Real.instMin.min fmax (instHDiv.hDiv Fmax n.cast).sqrt
```

### D006: `HighamBench.p20IsPowerOfTwo._proof_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `2ce92de675040573a86bb56eb1810ec5f97d8bfda24fdbdb86d7ca409b945411`

Type:

```lean
(instHAdd.hAdd 1 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D007: `HighamBench.p20RowScaleExponent`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `29d02b1d52e290d84959a21fdb5b56bedb818087267f5a5761566ac61ee44f83`

Type:

```lean
{n : Nat} → Real → (Fin n → Real) → Int
```

Fully explicit type:

```lean
{n : Nat} → (theta : Real) → (x : Fin n → Real) → Int
```

Definition body (one-level semantic boundary):

```lean
fun {n} theta x =>
  if hratio : Real.instLT.lt 0 (instHDiv.hDiv theta (HighamBench.p20InfNormVec x)) then Classical.choose ⋯ else 0
```

### D008: `HighamBench.p20RowScalingMatrix`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3f96f645eb64c245e0b38a5d18199fb79bd5c57f3797c0907d342150c82f8ed4`

Type:

```lean
{m n : Nat} → Real → Matrix (Fin m) (Fin n) Real → Matrix (Fin m) (Fin m) Real
```

Fully explicit type:

```lean
{m n : Nat} → (theta : Real) → (A : Matrix.{0, 0, 0} (Fin m) (Fin n) Real) → Matrix.{0, 0, 0} (Fin m) (Fin m) Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n} theta A => Matrix.diagonal fun i => HighamBench.p20RowScaleFactor theta (A i)
```

### D009: `HighamBench.p20RowScaleExponent._proof_1`

- Role: `local`
- Owner module: `HighamBench.P20Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `98ca612b4c0bcf1b2359d8bda7ebb2a662cde93e06fbc755f34335445f2c30c3`

Type:

```lean
∀ {n : Nat} (theta : Real) (x : Fin n → Real),
  Real.instLT.lt 0 (instHDiv.hDiv theta (HighamBench.p20InfNormVec x)) →
    Exists fun n_1 =>
      Set.instMembership.mem (Set.Ico (instHPow.hPow 2 n_1) (instHPow.hPow 2 (instHAdd.hAdd n_1 1)))
        (instHDiv.hDiv theta (HighamBench.p20InfNormVec x))
```

Fully explicit type:

```lean
∀ {n : Nat} (theta : Real) (x : Fin n → Real)
  (hratio :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        theta (@HighamBench.p20InfNormVec n x))),
  @Exists.{1} Int fun (n_1 : Int) =>
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ico.{0} Real
        (@PartialOrder.toPreorder.{0} Real
          (@SemilatticeInf.toPartialOrder.{0} Real
            (@Lattice.toSemilatticeInf.{0} Real
              (@DistribLattice.toLattice.{0} Real (@instDistribLatticeOfLinearOrder.{0} Real Real.linearOrder)))))
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int
            (@DivInvMonoid.toZPow.{0} Real
              (@GroupWithZero.toDivInvMonoid.{0} Real
                (@DivisionSemiring.toGroupWithZero.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast HighamBench.p20IsPowerOfTwo._proof_1))
          n_1)
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int
            (@DivInvMonoid.toZPow.{0} Real
              (@GroupWithZero.toDivInvMonoid.{0} Real
                (@DivisionSemiring.toGroupWithZero.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real (@Field.toSemifield.{0} Real Real.instField))))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast HighamBench.p20IsPowerOfTwo._proof_1))
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) n_1
            (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        theta (@HighamBench.p20InfNormVec n x))
```

### D010: `And`

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

### D011: `DivInvMonoid.toDiv`

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

### D012: `Exists`

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

### D013: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D014: `HDiv.hDiv`

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

### D015: `HMul.hMul`

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

### D016: `LE.le`

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

### D017: `LT.lt`

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

### D018: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D019: `Nat`

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

### D020: `Nat.instAtLeastTwoHAddOfNat`

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

### D021: `Nat.instNeZeroSucc`

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

### D022: `OfNat.ofNat`

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

### D023: `Real`

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

### D024: `Real.instAddGroup`

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

### D025: `Real.instDivInvMonoid`

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

### D026: `Real.instLE`

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

### D027: `Real.instLT`

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

### D028: `Real.instMul`

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

### D029: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5fc7a7becbc71d472fa1a28bd92d79b4c6ea4fdc643db7380031a2b890ca7e15`

Type:

```lean
NatCast Real
```

Fully explicit type:

```lean
NatCast.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D030: `Real.instZero`

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

### D031: `Real.lattice`

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

### D032: `Zero.toOfNat0`

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

### D034: `instHDiv`

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

### D035: `instHMul`

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

### D036: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4054f2341fdda887b2040c624c0867866ab56eabf3441d6ffc9451c94ae1663c`

Type:

```lean
LT Nat
```

Fully explicit type:

```lean
LT.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```

### D037: `instOfNatAtLeastTwo`

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

### D038: `instOfNatNat`

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

### D039: `ConditionallyCompleteLinearOrderBot.toOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.ConditionallyCompleteLattice.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8d4bfb1cedb616878ecbd86e2180bc7ca93b21716425a9954eeab125e930003f`

Type:

```lean
{α : Type u_5} → [self : ConditionallyCompleteLinearOrderBot α] → OrderBot α
```

Fully explicit type:

```lean
{α : Type u_5} →
  [self : ConditionallyCompleteLinearOrderBot.{u_5} α] →
    @OrderBot.{u_5} α
      (@Preorder.toLE.{u_5} α
        (@PartialOrder.toPreorder.{u_5} α
          (@SemilatticeSup.toPartialOrder.{u_5} α
            (@Lattice.toSemilatticeSup.{u_5} α
              (@ConditionallyCompleteLattice.toLattice.{u_5} α
                (@ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u_5} α
                  (@ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u_5} α self)))))))
```

Definition body (one-level semantic boundary):

```lean
fun α [self : ConditionallyCompleteLinearOrderBot α] => self.2
```

### D040: `DivInvMonoid.toZPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1e8b6758b3a3bf88b78eeff1bb4effb1dce39e6b9e38153dab79b664d58d89b5`

Type:

```lean
{M : Type u_2} → [DivInvMonoid M] → Pow M Int
```

Fully explicit type:

```lean
{M : Type u_2} → [DivInvMonoid.{u_2} M] → Pow.{u_2, 0} M Int
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : DivInvMonoid M] => { pow := fun x n => inst.zpow n x }
```

### D041: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D042: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `e7038d0981813ab904ddadd5c858e1d87d6d42413a72872c71b6e0413db6bb44`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → Fintype.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D043: `Finset.sup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finset.Lattice.Fold`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd4c14458f3cc53851b18c831b354790927e7783eeceddbd2bc8e0e17c3e5d98`

Type:

```lean
{α : Type u_2} → {β : Type u_3} → [inst : SemilatticeSup α] → [OrderBot α] → Finset β → (β → α) → α
```

Fully explicit type:

```lean
{α : Type u_2} →
  {β : Type u_3} →
    [inst : SemilatticeSup.{u_2} α] →
      [@OrderBot.{u_2} α
            (@Preorder.toLE.{u_2} α (@PartialOrder.toPreorder.{u_2} α (@SemilatticeSup.toPartialOrder.{u_2} α inst)))] →
        (s : Finset.{u_3} β) → (f : β → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [SemilatticeSup α] [inst_1 : OrderBot α] s f =>
  Finset.fold (fun x1 x2 => SemilatticeSup.toMax.max x1 x2) inst_1.bot f s
```

### D044: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `194413a784fbc0b27d0cb6b1ab67ed060210172bf16ba24045aa439e58f9a8c7`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Fully explicit type:

```lean
{α : Type u_1} → [Fintype.{u_1} α] → Finset.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D045: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D046: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D047: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `8eecda35a630fe4097c6149154c07645e87eaf089a78dde5ca01f180806c2a40`

Type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} → [Fintype m] → [Mul α] → [AddCommMonoid α] → HMul (Matrix l m α) (Matrix m n α) (Matrix l n α)
```

Fully explicit type:

```lean
{l : Type u_1} →
  {m : Type u_2} →
    {n : Type u_3} →
      {α : Type v} →
        [Fintype.{u_2} m] →
          [Mul.{v} α] →
            [AddCommMonoid.{v} α] →
              HMul.{max (max v u_2) u_1, max (max v u_3) u_2, max (max v u_3) u_1} (Matrix.{u_1, u_2, v} l m α)
                (Matrix.{u_2, u_3, v} m n α) (Matrix.{u_1, u_3, v} l n α)
```

Definition body (one-level semantic boundary):

```lean
fun {l} {m} {n} {α} [Fintype m] [Mul α] [AddCommMonoid α] =>
  { hMul := fun M N i k => dotProduct (fun j => M i j) fun j => N j k }
```

### D048: `Min.min`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `4781b8f14117c86f8d250ccd7a9bf20c2b8b6554a48ba0b45f9010ff26a72ea7`

Type:

```lean
{α : Type u} → [self : Min α] → α → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Min.{u} α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Min α] => self.1
```

### D049: `NNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `490ebc1f72b3ced8506e1bcbd0016d4c351adf097644509fd1dd17a93c4e950f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
Subtype fun r => Real.instLE.le 0 r
```

### D050: `NNReal.instConditionallyCompleteLinearOrderBot`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a6df35137b7f52b464ab762b2393c5d6b5cba77a839712e58984b3a00414c3af`

Type:

```lean
ConditionallyCompleteLinearOrderBot NNReal
```

Fully explicit type:

```lean
ConditionallyCompleteLinearOrderBot.{0} NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.conditionallyCompleteLinearOrderBot 0
```

### D051: `NNReal.toReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `b78a80825150cf81a49e8914dd12c5dfb7e284ed0e70b3449011ac3d3f49dc66`

Type:

```lean
NNReal → Real
```

Fully explicit type:

```lean
NNReal → Real
```

Definition body (one-level semantic boundary):

```lean
Subtype.val
```

### D052: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `6e24327ea908b1837083bb15aef27d593e950a2ff8ade81d8aa94bfe33b64450`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D053: `Real.instAddCommMonoid`

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

### D054: `Real.instMin`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d2cd90660c09f0530ecb3d8bd97eb9c8e1ed4fc9eebe2650e6a65a653c99fcb0`

Type:

```lean
Min Real
```

Fully explicit type:

```lean
Min.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ min := Real.inf✝ }
```

### D055: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D056: `Real.toNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `d5a5745fe197b17d74201a2db472f8ca23ff9fdb827ba67a427efe3c5468ae2e`

Type:

```lean
Real → NNReal
```

Fully explicit type:

```lean
(r : Real) → NNReal
```

Definition body (one-level semantic boundary):

```lean
fun r => ⟨Real.instMax.max r 0, ⋯⟩
```

### D057: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D058: `instSemilatticeSupNNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.NNReal.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2a6440af851e8806e3c58934c33bb1185e865186dfb38346ffc479f2e156fbfa`

Type:

```lean
SemilatticeSup NNReal
```

Fully explicit type:

```lean
SemilatticeSup.{0} NNReal
```

Definition body (one-level semantic boundary):

```lean
Nonneg.semilatticeSup
```

### D059: `Classical.choose`

- Role: `external-frontier`
- Owner module: `Init.Classical`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `b1c701cdfaf2d85710069fad282daeeed4f8640330d48f3d379fb221f4e4fb07`

Type:

```lean
{α : Sort u} → {p : α → Prop} → (Exists fun x => p x) → α
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (h : @Exists.{u} α fun (x : α) => p x) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {p} h => (Classical.indefiniteDescription p h).val
```

### D060: `DistribLattice.toLattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Lattice`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `081c5188b143552def8780e92ec3c58d8fefea20ca3c7cef110e3115c2be4fd6`

Type:

```lean
{α : Type u_1} → [self : DistribLattice α] → Lattice α
```

Fully explicit type:

```lean
{α : Type u_1} → [self : DistribLattice.{u_1} α] → Lattice.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : DistribLattice α] => self.1
```

### D061: `DivisionSemiring.toGroupWithZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Field.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a52dad8e67c4d0be4eb4eefa94c723afe9203f4246d76d8dff8eff9c866e5e6d`

Type:

```lean
{K : Type u_2} → [self : DivisionSemiring K] → GroupWithZero K
```

Fully explicit type:

```lean
{K : Type u_2} → [self : DivisionSemiring.{u_2} K] → GroupWithZero.{u_2} K
```

Definition body (one-level semantic boundary):

```lean
fun K self =>
  { toMul := self.toMul, mul_assoc := ⋯, toOne := self.toOne, one_mul := ⋯, mul_one := ⋯, npow := self.npow,
    npow_zero := ⋯, npow_succ := ⋯, toZero := self.toZero, zero_mul := ⋯, mul_zero := ⋯, toInv := self.toInv,
    toDiv := self.toDiv, div_eq_mul_inv := ⋯, zpow := self.zpow, zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯,
    toNontrivial := ⋯, inv_zero := ⋯, mul_inv_cancel := ⋯ }
```

### D062: `Field.toSemifield`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Field.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9a6353c2087dc0f4123f4079d947842f8b7bc1fc0c77de170382c04e31608fd4`

Type:

```lean
{K : Type u_1} → [Field K] → Semifield K
```

Fully explicit type:

```lean
{K : Type u_1} → [Field.{u_1} K] → Semifield.{u_1} K
```

Definition body (one-level semantic boundary):

```lean
fun {K} [inst : Field K] =>
  let __src := inst;
  { toSemiring := __src.toSemiring, mul_comm := ⋯, toInv := __src.toInv, toDiv := __src.toDiv, div_eq_mul_inv := ⋯,
    zpow := __src.zpow, zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯, toNontrivial := ⋯, inv_zero := ⋯,
    mul_inv_cancel := ⋯, toNNRatCast := __src.toNNRatCast, nnratCast_def := ⋯, nnqsmul := __src.nnqsmul,
    nnqsmul_def := ⋯ }
```

### D063: `GroupWithZero.toDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6a595375c8f1e40964d5f3eb28600b475a2aa8e42b16600c8200f3ad399bc2ef`

Type:

```lean
{G₀ : Type u} → [self : GroupWithZero G₀] → DivInvMonoid G₀
```

Fully explicit type:

```lean
{G₀ : Type u} → [self : GroupWithZero.{u} G₀] → DivInvMonoid.{u} G₀
```

Definition body (one-level semantic boundary):

```lean
fun G₀ self =>
  { toMonoid := self.toMonoid, toInv := self.toInv, toDiv := self.toDiv, div_eq_mul_inv := ⋯, zpow := self.zpow,
    zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯ }
```

### D064: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D065: `Int.instAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f3fe827ffb6fc81658773a6ada6451aeb9c1a54d32b216d8dede8eae9142825b`

Type:

```lean
Add Int
```

Fully explicit type:

```lean
Add.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ add := Int.add }
```

### D066: `Lattice.toSemilatticeInf`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Lattice`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `81af889ae7d07b4641fdf75ee1ac1bcb7775ec72bd7fe51d0cb1c550f7251505`

Type:

```lean
{α : Type u} → [self : Lattice α] → SemilatticeInf α
```

Fully explicit type:

```lean
{α : Type u} → [self : Lattice.{u} α] → SemilatticeInf.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toPartialOrder := self.toPartialOrder, inf := self.inf, inf_le_left := ⋯, inf_le_right := ⋯, le_inf := ⋯ }
```

### D067: `Matrix.diagonal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `82e46083880c6f749e6150ebf3a785ee7efb7663d9d75b703957fe860f297e3d`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → (n → α) → Matrix n n α
```

Fully explicit type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq.{u_3 + 1} n] → [Zero.{v} α] → (d : n → α) → Matrix.{u_3, u_3, v} n n α
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] d => EquivLike.toFunLike.coe Matrix.of fun i j => ite (Eq i j) (d i) 0
```

### D068: `Membership.mem`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D069: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

Fully explicit type:

```lean
(n : Nat) → Prop
```

### D070: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `0bfdacbe07f6cbb8995b354e36299fd742f29398c188d7cc23dedcdc47f57a9a`

Type:

```lean
Prop → Prop
```

Fully explicit type:

```lean
(a : Prop) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D071: `PartialOrder.toPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `079686fa1ec6d596bcdb475c56a12b7f5a0594bf346c64220c2c992e0f0aae3b`

Type:

```lean
{α : Type u_2} → [self : PartialOrder α] → Preorder α
```

Fully explicit type:

```lean
{α : Type u_2} → [self : PartialOrder.{u_2} α] → Preorder.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PartialOrder α] => self.1
```

### D072: `Real.decidableLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `def93575a13821d7d42b557cb9b973eede26ae12bbb8b60b1f0a302bf95a5a42`

Type:

```lean
(a b : Real) → Decidable (Real.instLT.lt a b)
```

Fully explicit type:

```lean
(a b : Real) → Decidable (@LT.lt.{0} Real Real.instLT a b)
```

Definition body (one-level semantic boundary):

```lean
fun a b => inferInstance
```

### D073: `Real.instField`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `64a3a49f867e24195f55b1d8c28f24c2ac0fad4a3ad0fa540db847ac229e53d3`

Type:

```lean
Field Real
```

Fully explicit type:

```lean
Field.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ toCommRing := Real.commRing, toInv := Real.instDivInvMonoid.toInv, toDiv := Real.instDivInvMonoid.toDiv,
  div_eq_mul_inv := ⋯, zpow := Real.instDivInvMonoid.zpow, zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯,
  toNontrivial := Real.instNontrivial, toNNRatCast := Real.instNNRatCast, toRatCast := Real.instRatCast,
  mul_inv_cancel := Real.instField._proof_5, inv_zero := Real.instField._proof_6, nnratCast_def := ⋯,
  nnqsmul := fun x => instHMul.hMul x.cast, nnqsmul_def := Real.instField._proof_1, ratCast_def := ⋯,
  qsmul := fun x => instHMul.hMul x.cast, qsmul_def := Real.instField._proof_2 }
```

### D074: `Real.linearOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f9047b32ccb57072950d165d85fa407659039ec6ac3d859d4f35ab0efe02a4d9`

Type:

```lean
LinearOrder Real
```

Fully explicit type:

```lean
LinearOrder.{0} Real
```

Definition body (one-level semantic boundary):

```lean
Lattice.toLinearOrder Real
```

### D075: `Semifield.toDivisionSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Field.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `a1b771abeff9bbbdcce988134973a1a367c44a340bcd29acb0cc44b8d6a2e55c`

Type:

```lean
{K : Type u_2} → [self : Semifield K] → DivisionSemiring K
```

Fully explicit type:

```lean
{K : Type u_2} → [self : Semifield.{u_2} K] → DivisionSemiring.{u_2} K
```

Definition body (one-level semantic boundary):

```lean
fun K self =>
  { toSemiring := self.toSemiring, toInv := self.toInv, toDiv := self.toDiv, div_eq_mul_inv := ⋯, zpow := self.zpow,
    zpow_zero' := ⋯, zpow_succ' := ⋯, zpow_neg' := ⋯, toNontrivial := ⋯, inv_zero := ⋯, mul_inv_cancel := ⋯,
    toNNRatCast := self.toNNRatCast, nnratCast_def := ⋯, nnqsmul := self.nnqsmul, nnqsmul_def := ⋯ }
```

### D076: `SemilatticeInf.toPartialOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Lattice`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `893084ece5bf8c05fbd4a1c81599a96f6f81888e21ce27ed05c0d273c70e59b0`

Type:

```lean
{α : Type u} → [self : SemilatticeInf α] → PartialOrder α
```

Fully explicit type:

```lean
{α : Type u} → [self : SemilatticeInf.{u} α] → PartialOrder.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SemilatticeInf α] => self.1
```

### D077: `Set`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D078: `Set.Ico`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Interval.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `48aa2cf5736dd57481b68491490245577ea0b7b50fe2429fb88f717769ea5830`

Type:

```lean
{α : Type u_1} → [Preorder α] → α → α → Set α
```

Fully explicit type:

```lean
{α : Type u_1} → [Preorder.{u_1} α] → (a b : α) → Set.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Preorder α] a b => setOf fun x => And (inst.le a x) (inst.lt x b)
```

### D079: `Set.instMembership`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D080: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a2551097d29bac847f3c59e8213b5882afd4a95e9247c2382e8bce33011974b5`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (c → α) → (Not c → α) → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t : c → α) → (e : Not c → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h e t
```

### D081: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a1534bcd3e1888406ac787d30eeff8a284cb6688c23f5e8de09351dda91a280c`

Type:

```lean
Add Nat
```

Fully explicit type:

```lean
Add.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D082: `instDecidableEqFin`

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

### D083: `instDistribLatticeOfLinearOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Lattice`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `e4ffbef8db4dacfffb209c39b37d22abe6f018d4ed65067cd1eaf977e7da1bcb`

Type:

```lean
{α : Type u} → [LinearOrder α] → DistribLattice α
```

Fully explicit type:

```lean
{α : Type u} → [LinearOrder.{u} α] → DistribLattice.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [LinearOrder α] => { toLattice := LinearOrder.toLattice, le_sup_inf := ⋯ }
```

### D084: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D085: `instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d01cf83431e28a96433c57a624e20a771e5e0ddc02355969c5044adf1ba168a5`

Type:

```lean
{n : Nat} → OfNat Int n
```

Fully explicit type:

```lean
{n : Nat} → OfNat.{0} Int n
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { ofNat := Int.ofNat n }
```

## Complete local imported sources

### `HighamBench.Core`

Path: `paper_bencmark/highambench/shared/HighamBench/Core.lean`
SHA-256: `8c84e05c04f4245e067d3a971dafa45bcfe92f55bbc24f2305964a8e2b9bd55a`

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# HighamBench common core

This file is deliberately independent of the evaluated library. It contains
only the floating-point model and notation used by more than one benchmark
paper.
-/

namespace HighamBench

open scoped BigOperators

/-- The part of the usual floating-point model needed for ordinary summation. -/
structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

/-- Higham's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- The denominator in `gamma u n` is positive. -/
def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Left-to-right recursive summation, with a one-element sum kept exact. -/
noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

end HighamBench
```

### `HighamBench.P20Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P20Definitions.lean`
SHA-256: `33554be89414f9d3fa27232131e6817fcc7f2017087e8bae4f59ceb4e2cfa4ea`

```lean
import HighamBench.Core
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

/-- The explicit finite maximum of the absolute vector coefficients used as
the infinity norm around equations (3.1)--(3.4). -/
noncomputable def p20InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => Real.toNNReal |x i|) : NNReal) : ℝ)

/-- Scale a finite row or column by a real power-of-two factor. -/
def p20ScaleVec {n : ℕ} (lambda : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda * x i

/-- The largest safe scaled-input magnitude from equation (3.2). -/
noncomputable def p20ScalingThreshold (n : ℕ) (fmax Fmax : ℝ) : ℝ :=
  min fmax (Real.sqrt (Fmax / (n : ℝ)))

/-- Exact powers of two used for the diagonal scaling factors in (3.1). -/
def p20IsPowerOfTwo (lambda : ℝ) : Prop :=
  ∃ exponent : ℤ, lambda = (2 : ℝ) ^ exponent

/-- Select the exponent whose power of two lies immediately below
`theta / ‖x‖∞`. The fallback is irrelevant for the positive ratios required
by equation (3.4a). -/
noncomputable def p20RowScaleExponent {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℤ :=
  if hratio : 0 < theta / p20InfNormVec x then
    Classical.choose
      (exists_mem_Ico_zpow hratio (by norm_num : (1 : ℝ) < 2))
  else
    0

/-- The row-specific power-of-two factor `lambda_i` selected for (3.4a). -/
noncomputable def p20RowScaleFactor {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℝ :=
  (2 : ℝ) ^ p20RowScaleExponent theta x

/-- The diagonal matrix `Lambda` from equation (3.1). -/
noncomputable def p20RowScalingMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => p20RowScaleFactor theta (A i))

/-- The exactly scaled input `Lambda A` from equation (3.1). -/
noncomputable def p20LeftScaledMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  p20RowScalingMatrix theta A * A

/-- Paper-scoped rectangular infinity norm (maximum absolute row sum). -/
noncomputable def p20InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

/-- The input-underflow part of the simplified single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowBound {m n q : ℕ}
    (theta gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The accumulation-underflow part of the simplified single-word bound
(3.26). -/
noncomputable def p20SingleAccumUnderflowBound {m n q : ℕ}
    (theta Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * (theta⁻¹) ^ 2 * Gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The input-rounding term in the multiword bound (4.32). -/
def p20MultiInputRoundingCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p

/-- The accumulation-rounding term in the multiword bound (4.32). -/
def p20MultiAccumRoundingCoefficient (n p : ℕ) (U : ℝ) : ℝ :=
  ((n : ℝ) + (p : ℝ) ^ 2) * U

/-- The range-unrestricted coefficient in the multiword bound (4.33). -/
def p20MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  p20MultiInputRoundingCoefficient p u +
    p20MultiAccumRoundingCoefficient n p U

/-- The input-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

/-- The accumulation-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

/-- The complete narrow-range coefficient in the multiword bound (4.32). -/
noncomputable def p20MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p20MultiRangeFreeCoefficient n p u U +
    p20MultiInputUnderflowCoefficient n p u theta gmin +
      p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- Apply a scalar coefficient to the product of the two rectangular matrix
infinity norms appearing in (3.26), (4.32), and (4.33). -/
noncomputable def p20NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p20InfNormRect A * p20InfNormRect B

/-! ## Multiword execution model for Theorem 4.1 -/

/-- A finite rectangular real matrix in the P20 model. -/
abbrev P20Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The unit roundoff `2^(-t)` of a binary format with `t` precision bits. -/
noncomputable def p20UnitRoundoff (precision : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ precision

/-- The smallest positive normalized value of a binary format. -/
noncomputable def p20MinNormal (minExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ minExponent

/-- The largest finite value of the binary format used in Model 1. -/
noncomputable def p20MaxFinite (precision : ℕ) (maxExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ maxExponent * (2 - 2 * p20UnitRoundoff precision)

/-- The `g_min` or `G_min` envelope from (2.1)--(2.2). -/
noncomputable def p20UnderflowEnvelope (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) : ℝ :=
  match hasSubnormals with
  | false => p20MinNormal minExponent / 2
  | true => p20UnitRoundoff precision * p20MinNormal minExponent

/-- A precision-parametrized binary floating-point format from Model 1. -/
structure P20BinaryFormatFamily (ι : Type*) where
  precision : ι → ℕ
  minExponent : ι → ℤ
  maxExponent : ι → ℤ
  hasSubnormals : ι → Bool
  precision_pos : ∀ t, 0 < precision t
  exponent_range_nonempty : ∀ t, minExponent t ≤ maxExponent t

/-- Unit roundoff of one member of a format family. -/
noncomputable def p20FormatUnitRoundoff {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnitRoundoff (format.precision t)

/-- Largest finite value of one member of a format family. -/
noncomputable def p20FormatMaxFinite {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20MaxFinite (format.precision t) (format.maxExponent t)

/-- Underflow envelope of one member of a format family. -/
noncomputable def p20FormatUnderflowEnvelope {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnderflowEnvelope (format.precision t) (format.minExponent t)
    (format.hasSubnormals t)

/-- Model 1: input and accumulation formats, their nesting, and the two
rounding models (2.3)--(2.4). The maps represent operations for which overflow
does not occur. -/
structure P20Model1 (ι : Type*) where
  inputFormat : P20BinaryFormatFamily ι
  accumulationFormat : P20BinaryFormatFamily ι
  accumulation_precision : ∀ t,
    inputFormat.precision t ≤ accumulationFormat.precision t
  accumulation_range : ∀ t,
    accumulationFormat.minExponent t ≤ inputFormat.minExponent t ∧
      inputFormat.maxExponent t ≤ accumulationFormat.maxExponent t
  inputRound : ι → ℝ → ℝ
  inputDelta : ι → ℝ → ℝ
  inputEta : ι → ℝ → ℝ
  input_rounding_equation : ∀ t x,
    inputRound t x = x * (1 + inputDelta t x) + inputEta t x
  input_delta_bound : ∀ t x,
    |inputDelta t x| ≤ p20FormatUnitRoundoff inputFormat t
  input_eta_bound : ∀ t x,
    |inputEta t x| ≤ p20FormatUnderflowEnvelope inputFormat t
  input_error_exclusive : ∀ t x, inputEta t x * inputDelta t x = 0
  accumulationRound : ι → ℝ → ℝ
  accumulationDelta : ι → ℝ → ℝ
  accumulationEta : ι → ℝ → ℝ
  accumulation_rounding_equation : ∀ t x,
    accumulationRound t x =
      x * (1 + accumulationDelta t x) + accumulationEta t x
  accumulation_delta_bound : ∀ t x,
    |accumulationDelta t x| ≤
      p20FormatUnitRoundoff accumulationFormat t
  accumulation_eta_bound : ∀ t x,
    |accumulationEta t x| ≤
      p20FormatUnderflowEnvelope accumulationFormat t
  accumulation_error_exclusive : ∀ t x,
    accumulationEta t x * accumulationDelta t x = 0

/-- The input-format unit roundoff `u` of Model 1. -/
noncomputable def p20InputUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.inputFormat t

/-- The accumulation-format unit roundoff `U` of Model 1. -/
noncomputable def p20AccumUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.accumulationFormat t

/-- The input-format underflow envelope `g_min` of Model 1. -/
noncomputable def p20InputUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.inputFormat t

/-- The accumulation-format underflow envelope `G_min` of Model 1. -/
noncomputable def p20AccumUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.accumulationFormat t

/-- The format-derived scaling threshold `theta` from (3.2). -/
noncomputable def p20ModelScalingThreshold {ι : Type*}
    (n : ℕ) (model : P20Model1 ι) (t : ι) : ℝ :=
  p20ScalingThreshold n
    (p20FormatMaxFinite model.inputFormat t)
    (p20FormatMaxFinite model.accumulationFormat t)

/-- Exact row scaling by the diagonal entries of `Lambda`. -/
def p20ScaleRows {m n : ℕ} (lambda : Fin m → ℝ)
    (A : P20Matrix m n) : P20Matrix m n :=
  fun i j => lambda i * A i j

/-- Exact column scaling by the diagonal entries of `M`. -/
def p20ScaleColumns {n q : ℕ} (B : P20Matrix n q)
    (mu : Fin q → ℝ) : P20Matrix n q :=
  fun i j => B i j * mu j

/-- The maximal-power-of-two scaling rule inherited from (3.4a)--(3.4b).
The zero-vector branch records an explicit harmless convention omitted by the
paper. -/
def p20MaximalPowerTwoScale (theta vectorNorm lambda : ℝ) : Prop :=
  p20IsPowerOfTwo lambda ∧ 0 < lambda ∧
    ((vectorNorm = 0 ∧ lambda = 1) ∨
      (0 < vectorNorm ∧ theta / (2 * vectorNorm) < lambda ∧
        lambda ≤ theta / vectorNorm))

/-- An accumulation-format inner product. Each multiply-add result is rounded
by the accumulation map from Model 1. -/
noncomputable def p20AccumulatedInnerProduct {n : ℕ}
    (round : ℝ → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (List.ofFn fun k : Fin n => x k * y k).foldl
    (fun sum product => round (sum + product)) 0

/-- The retained word-index pairs from (4.31), in lexicographic execution
order. -/
def p20RetainedWordPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.ofFn fun i : Fin p =>
    (List.ofFn fun j : Fin p => (i, j)).filter
      (fun pair => decide (pair.1.val + pair.2.val < p))).flatten

/-- The accumulated expression inside the inverse scalings in (4.31): retain
precisely the word pairs with `i+j<p`, weight them by `u^(i+j)`, and round
their running sum in the accumulation format. -/
noncomputable def p20RetainedWordProduct {m n q p : ℕ}
    (round : ℝ → ℝ) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    (p20RetainedWordPairs p).foldl
      (fun sum pair =>
        round
          (sum + u ^ (pair.1.val + pair.2.val) *
            p20AccumulatedInnerProduct round (Aword pair.1 row)
              (fun k => Bword pair.2 k col))) 0

/-- Undo the diagonal row and column scalings around the retained word
product, as in (4.31). -/
noncomputable def p20UnscaleProduct {m q : ℕ} (lambda : Fin m → ℝ)
    (mu : Fin q → ℝ) (C : P20Matrix m q) : P20Matrix m q :=
  fun i j => (lambda i)⁻¹ * C i j * (mu j)⁻¹

/-- One computed instance of the scaled p-word algorithm (4.29)--(4.31).
The scaling clauses include the lower endpoints used in the derivation of
Theorem 4.1, not only the upper bounds printed in its statement. -/
structure P20MultiwordRun (m n q p : ℕ) (ι : Type*) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20Model1 ι
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : ι → Fin m → ℝ
  columnScale : ι → Fin q → ℝ
  row_scaling_rule : ∀ t i,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (A i)) (rowScale t i)
  column_scaling_rule : ∀ t j,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (fun i => B i j)) (columnScale t j)
  scaled_A_bound : ∀ t i j,
    |p20ScaleRows (rowScale t) A i j| ≤
      p20ModelScalingThreshold n model t
  scaled_B_bound : ∀ t i j,
    |p20ScaleColumns B (columnScale t) i j| ≤
      p20ModelScalingThreshold n model t
  Aword : ι → Fin p → P20Matrix m n
  Bword : ι → Fin p → P20Matrix n q
  Aword_equation : ∀ t i row col,
    Aword t i row col = model.inputRound t
      ((p20ScaleRows (rowScale t) A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Aword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  Bword_equation : ∀ t i row col,
    Bword t i row col = model.inputRound t
      ((p20ScaleColumns B (columnScale t) row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Bword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  computed : ι → P20Matrix m q
  computed_equation : ∀ t,
    computed t = p20UnscaleProduct (rowScale t) (columnScale t)
      (p20RetainedWordProduct (model.accumulationRound t)
        (p20InputUnitRoundoff model t) (Aword t) (Bword t))

/-- Reconstruct `A` from all `p` input words and undo `Lambda`, as in (4.18). -/
noncomputable def p20AWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m n :=
  fun row col =>
    (run.rowScale t row)⁻¹ *
      ∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Aword t i row col

/-- Reconstruct `B` from all `p` input words and undo `M`, as in (4.19). -/
noncomputable def p20BWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Bword t i row col) *
      (run.columnScale t col)⁻¹

/-- The retained part of (4.31) with exact inner products and exact summation.
Its difference from the computed value isolates accumulation-format errors. -/
noncomputable def p20ExactRetainedWordProduct {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The products omitted from (4.31), namely all word pairs with `i+j>=p`. -/
noncomputable def p20OmittedWordTail {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The actual normwise forward error of one execution of (4.31). -/
noncomputable def p20MultiwordForwardError {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : ℝ :=
  p20InfNormRect (run.computed t - run.A * run.B)

/-- The combined first-order scale whose square classifies the terms hidden
by `lesssim` in (4.26)--(4.32). Dimensions and `p` are fixed along the filter. -/
noncomputable def p20MultiwordPrecisionScale {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) : ι → ℝ :=
  fun t =>
    p20InputUnitRoundoff run.model t ^ p +
      p20InputUnitRoundoff run.model t ^ (p - 1) *
        (p20ModelScalingThreshold n run.model t)⁻¹ *
          p20InputUnderflowEnvelope run.model t +
      p20AccumUnitRoundoff run.model t +
      (p20ModelScalingThreshold n run.model t)⁻¹ ^ 2 *
        p20AccumUnderflowEnvelope run.model t

/-- A scalar or norm remainder that is second order in the precision scale. -/
def p20SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t => scale t ^ 2

/-- A precise first-order interpretation of the paper's `lesssim`: the
displayed inequality holds modulo an explicitly second-order remainder. -/
def p20FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p20SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The exact decomposition identities from (4.18)--(4.24), split into
relative-rounding and underflow parts. These identities tie every subsequent
contribution to the words and computed matrix in `run`. -/
structure P20MultiwordErrorData {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) where
  AInputRoundingError : ι → P20Matrix m n
  AInputUnderflowError : ι → P20Matrix m n
  BInputRoundingError : ι → P20Matrix n q
  BInputUnderflowError : ι → P20Matrix n q
  accumulationRoundingError : ι → P20Matrix m q
  accumulationUnderflowError : ι → P20Matrix m q
  A_decomposition : ∀ t,
    run.A = p20AWordApproximation run t + AInputRoundingError t +
      AInputUnderflowError t
  B_decomposition : ∀ t,
    run.B = p20BWordApproximation run t + BInputRoundingError t +
      BInputUnderflowError t
  retained_partition : ∀ t,
    p20ExactRetainedWordProduct run t =
      p20AWordApproximation run t * p20BWordApproximation run t -
        p20OmittedWordTail run t
  accumulation_decomposition : ∀ t,
    run.computed t = p20ExactRetainedWordProduct run t +
      accumulationRoundingError t + accumulationUnderflowError t
  A_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    AInputRoundingError t = 0
  B_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    BInputRoundingError t = 0
  A_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    AInputUnderflowError t = 0
  B_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    BInputUnderflowError t = 0
  accumulation_rounding_zero : ∀ t, run.model.accumulationDelta t = 0 →
    accumulationRoundingError t = 0
  accumulation_underflow_zero : ∀ t, run.model.accumulationEta t = 0 →
    accumulationUnderflowError t = 0

/-- The first-order input-rounding contribution: the two linear decomposition
errors and the omitted `i+j>=p` tail. -/
noncomputable def p20InputRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputRoundingError t * run.B) -
    run.A * data.BInputRoundingError t - p20OmittedWordTail run t

/-- The two linear input-underflow contributions. -/
noncomputable def p20InputUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputUnderflowError t * run.B) -
    run.A * data.BInputUnderflowError t

/-- The accumulation-rounding contribution in the exact computed output. -/
def p20AccumRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationRoundingError t

/-- The accumulation-underflow contribution in the exact computed output. -/
def p20AccumUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationUnderflowError t

/-- The exact residual after removing the four displayed first-order
contributions from the actual computed forward-error matrix. -/
noncomputable def p20ForwardRemainder {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) : P20Matrix m q :=
  run.computed t - run.A * run.B - p20InputRoundingContribution data t -
    p20InputUnderflowContribution data t -
      p20AccumRoundingContribution data t -
        p20AccumUnderflowContribution data t

/-- Exact additive decomposition of the computed forward error. -/
theorem p20ForwardError_decomposition {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) :
    run.computed t - run.A * run.B =
      p20InputRoundingContribution data t +
        p20InputUnderflowContribution data t +
          p20AccumRoundingContribution data t +
            p20AccumUnderflowContribution data t +
              p20ForwardRemainder run data t := by
  unfold p20ForwardRemainder
  abel

/-- The four-source propagation certificate for the derivation
(4.18)--(4.28). It stores source-derived component estimates and a second-order
remainder, but not the final bound (4.32). -/
structure P20MultiwordForwardAnalysis {m n q p : ℕ} {ι : Type*}
    {l : Filter ι} (run : P20MultiwordRun m n q p ι) where
  data : P20MultiwordErrorData run
  input_rounding_bound : ∀ t,
    p20InfNormRect (p20InputRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputRoundingCoefficient p
          (p20InputUnitRoundoff run.model t)) run.A run.B
  input_underflow_bound : ∀ t,
    p20InfNormRect (p20InputUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputUnderflowCoefficient n p
          (p20InputUnitRoundoff run.model t)
          (p20ModelScalingThreshold n run.model t)
          (p20InputUnderflowEnvelope run.model t)) run.A run.B
  accumulation_rounding_bound : ∀ t,
    p20InfNormRect (p20AccumRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumRoundingCoefficient n p
          (p20AccumUnitRoundoff run.model t)) run.A run.B
  accumulation_underflow_bound : ∀ t,
    p20InfNormRect (p20AccumUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumUnderflowCoefficient n p
          (p20ModelScalingThreshold n run.model t)
          (p20AccumUnderflowEnvelope run.model t)) run.A run.B
  remainder_second_order :
    p20SecondOrderAt l (p20MultiwordPrecisionScale run)
      (fun t => p20InfNormRect (p20ForwardRemainder run data t))

/-- Dot-notation projection of the fixed higher-order remainder. -/
noncomputable def P20MultiwordForwardAnalysis.remainder
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20ForwardRemainder run analysis.data

/-- Dot-notation projection of the fixed input-rounding contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputRoundingContribution analysis.data

/-- Dot-notation projection of the fixed input-underflow contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputUnderflowContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-rounding contribution. -/
def P20MultiwordForwardAnalysis.accumulationRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumRoundingContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-underflow contribution. -/
def P20MultiwordForwardAnalysis.accumulationUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumUnderflowContribution analysis.data

/-- Dot-notation form of the exact additive decomposition. -/
theorem P20MultiwordForwardAnalysis.error_decomposition
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) (t : ι) :
    run.computed t - run.A * run.B =
      analysis.inputRoundingContribution t +
        analysis.inputUnderflowContribution t +
          analysis.accumulationRoundingContribution t +
            analysis.accumulationUnderflowContribution t +
              analysis.remainder t := by
  exact p20ForwardError_decomposition run analysis.data t

/-- A proof-carrying execution of every hypothesis and intermediate error
category used to obtain Theorem 4.1. -/
structure P20Theorem41Execution (m n q p : ℕ) (ι : Type*)
    (l : Filter ι) where
  run : P20MultiwordRun m n q p ι
  analysis : P20MultiwordForwardAnalysis (l := l) run

end HighamBench
```
