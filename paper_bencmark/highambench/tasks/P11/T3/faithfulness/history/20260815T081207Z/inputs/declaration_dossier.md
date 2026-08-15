# Declaration dossier for P11-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p11_t3_orthogonality_defect_bound {n : ℕ}
    (A dA Q R Rinv : P11Matrix n) (e a d rho : ℝ)
    (hQR : p11MatMul n Q R = A + dA)
    (hInv : p11MatMul n R Rinv = p11Identity n)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hd : 0 ≤ d) (hrho : 0 ≤ rho)
    (hE : p11FrobNorm (p11NormalEquationResidual A R) ≤ e)
    (hA : p11FrobNorm A ≤ a) (hdA : p11FrobNorm dA ≤ d)
    (hRinv : p11FrobNorm Rinv ≤ rho) :
    p11FrobNorm (p11OrthogonalityDefect Q) ≤
      rho ^ 2 * (e + 2 * a * d + d ^ 2)
```

## Elaborated target type

```lean
∀ {n : Nat} (A dA Q R Rinv : HighamBench.P11Matrix n) (e a d rho : Real),
  Eq (HighamBench.p11MatMul n Q R) (instHAdd.hAdd A dA) →
    Eq (HighamBench.p11MatMul n R Rinv) (HighamBench.p11Identity n) →
      Real.instLE.le 0 e →
        Real.instLE.le 0 a →
          Real.instLE.le 0 d →
            Real.instLE.le 0 rho →
              Real.instLE.le (HighamBench.p11FrobNorm (HighamBench.p11NormalEquationResidual A R)) e →
                Real.instLE.le (HighamBench.p11FrobNorm A) a →
                  Real.instLE.le (HighamBench.p11FrobNorm dA) d →
                    Real.instLE.le (HighamBench.p11FrobNorm Rinv) rho →
                      Real.instLE.le (HighamBench.p11FrobNorm (HighamBench.p11OrthogonalityDefect Q))
                        (instHMul.hMul (instHPow.hPow rho 2)
                          (instHAdd.hAdd (instHAdd.hAdd e (instHMul.hMul (instHMul.hMul 2 a) d)) (instHPow.hPow d 2)))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (A dA Q R Rinv : HighamBench.P11Matrix n) (e a d rho : Real)
  (hQR :
    @Eq.{1} (HighamBench.P11Matrix n) (HighamBench.p11MatMul n Q R)
      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P11Matrix n) (HighamBench.P11Matrix n) (HighamBench.P11Matrix n)
        (@instHAdd.{0} (HighamBench.P11Matrix n) (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd)) A dA))
  (hInv : @Eq.{1} (HighamBench.P11Matrix n) (HighamBench.p11MatMul n R Rinv) (HighamBench.p11Identity n))
  (he : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e)
  (ha : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hd : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d)
  (hrho : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) rho)
  (hE : @LE.le.{0} Real Real.instLE (@HighamBench.p11FrobNorm n (@HighamBench.p11NormalEquationResidual n A R)) e)
  (hA : @LE.le.{0} Real Real.instLE (@HighamBench.p11FrobNorm n A) a)
  (hdA : @LE.le.{0} Real Real.instLE (@HighamBench.p11FrobNorm n dA) d)
  (hRinv : @LE.le.{0} Real Real.instLE (@HighamBench.p11FrobNorm n Rinv) rho),
  @LE.le.{0} Real Real.instLE (@HighamBench.p11FrobNorm n (@HighamBench.p11OrthogonalityDefect n Q))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) rho
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) e
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              a)
            d))
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid)) d
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P11Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P11Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P11Matrix`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D002: `HighamBench.p11FrobNorm`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P11Matrix n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => (Finset.univ.sum fun i => Finset.univ.sum fun j => instHPow.hPow (A i j) 2).sqrt
```

### D003: `HighamBench.p11Identity`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
(n : Nat) → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
(n : Nat) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n => 1
```

### D004: `HighamBench.p11MatMul`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
(n : Nat) → HighamBench.P11Matrix n → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
(n : Nat) → (A B : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D005: `HighamBench.p11NormalEquationResidual`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A R : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A R =>
  instHSub.hSub (HighamBench.p11MatMul n (HighamBench.p11Transpose R) R)
    (HighamBench.p11MatMul n (HighamBench.p11Transpose A) A)
```

### D006: `HighamBench.p11OrthogonalityDefect`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (Q : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} Q => instHSub.hSub (HighamBench.p11Identity n) (HighamBench.p11MatMul n (HighamBench.p11Transpose Q) Q)
```

### D007: `HighamBench.p11Transpose`

- Role: `local`
- Owner module: `HighamBench.P11Definitions`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{n : Nat} → HighamBench.P11Matrix n → HighamBench.P11Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (A : HighamBench.P11Matrix n) → HighamBench.P11Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} A => Matrix.transpose A
```

### D008: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D009: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D010: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D011: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D012: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D013: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D014: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D015: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D016: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D017: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`

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

### D018: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`

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

### D019: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D020: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D021: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D022: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D023: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D024: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D025: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D026: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D027: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D028: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D029: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D030: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D031: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D032: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D033: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D034: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D035: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D036: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSub.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D037: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D038: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D039: `Matrix.one`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Diagonal`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{n : Type u_3} → {α : Type v} → [DecidableEq n] → [Zero α] → [One α] → One (Matrix n n α)
```

Fully explicit type:

```lean
{n : Type u_3} →
  {α : Type v} → [DecidableEq.{u_3 + 1} n] → [Zero.{v} α] → [One.{v} α] → One.{max v u_3} (Matrix.{u_3, u_3, v} n n α)
```

Definition body (one-level semantic boundary):

```lean
fun {n} {α} [DecidableEq n] [Zero α] [One α] => { one := Matrix.diagonal fun x => 1 }
```

### D040: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub α] → Sub (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Sub.{v} α] → Sub.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Sub α] => Pi.instSub
```

### D041: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D042: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D043: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D044: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
Sub Real
```

Fully explicit type:

```lean
Sub.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D045: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D046: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D047: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Fully explicit type:

```lean
{α : Type u_1} → [Sub.{u_1} α] → HSub.{u_1, u_1, u_1} α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D048: `Matrix.transpose`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → Matrix m n α → Matrix n m α
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → (M : Matrix.{u_2, u_3, v} m n α) → Matrix.{u_3, u_2, v} n m α
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} M => EquivLike.toFunLike.coe Matrix.of fun x y => M y x
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

### `HighamBench.P11Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P11Definitions.lean`
SHA-256: `d30af6550e76d4083f8958fd38563533a67d33dbfaf20349679d355a37a5e8f1`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- Square real matrices used for the finite P11 certificates. -/
abbrev P11Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Matrix multiplication in the P11 setting. -/
noncomputable def p11MatMul (n : ℕ) (A B : P11Matrix n) : P11Matrix n :=
  A * B

/-- Matrix transpose in the P11 setting. -/
def p11Transpose {n : ℕ} (A : P11Matrix n) : P11Matrix n :=
  A.transpose

/-- The identity matrix. -/
def p11Identity (n : ℕ) : P11Matrix n :=
  1

/-- Explicit Frobenius norm for the condition-neutral public statements. -/
noncomputable def p11FrobNorm {n : ℕ} (A : P11Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- Explicit Euclidean norm for a finite real vector. -/
noncomputable def p11VecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Matrix-vector multiplication. -/
noncomputable def p11MatVec {n : ℕ} (A : P11Matrix n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  A.mulVec x

/-- The loss-of-orthogonality matrix appearing in Theorem 1(7). -/
noncomputable def p11OrthogonalityDefect {n : ℕ}
    (Q : P11Matrix n) : P11Matrix n :=
  p11Identity n - p11MatMul n (p11Transpose Q) Q

/-- The normal-equations residual in Theorem 1(5). -/
noncomputable def p11NormalEquationResidual {n : ℕ}
    (A R : P11Matrix n) : P11Matrix n :=
  p11MatMul n (p11Transpose R) R -
    p11MatMul n (p11Transpose A) A

/-- The exact inner residual in the appendix derivation of Theorem 1(7). -/
noncomputable def p11DefectCore {n : ℕ}
    (A dA R : P11Matrix n) : P11Matrix n :=
  p11NormalEquationResidual A R -
    p11MatMul n (p11Transpose A) dA -
    p11MatMul n (p11Transpose dA) A -
    p11MatMul n (p11Transpose dA) dA

end HighamBench
```
