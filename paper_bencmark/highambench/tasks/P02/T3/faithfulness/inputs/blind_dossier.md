# Blind Lean declaration dossier

Translate only the mathematical proposition represented below. No paper identity,
source prose, task metadata, theorem name, proof, or benchmark commentary is included.
Do not use tools or inspect any filesystem content.

## Elaborated target type

```lean
∀ (fp : LocalDef002) (n K : Nat) (x y : Fin (instHAdd.hAdd n 1) → Real),
  instLENat.le 3 K →
    Real.instLE.le (instHMul.hMul (instHMul.hMul 8 (instHAdd.hAdd n 1).cast) fp.u) 1 →
      Real.instLE.le (abs (instHSub.hSub (LocalDef005 fp K x y) (LocalDef007 x y)))
        (instHAdd.hAdd
          (instHMul.hMul
            (instHAdd.hAdd fp.u
              (instHMul.hMul 2
                (instHPow.hPow (LocalDef008 fp.u (instHSub.hSub (instHMul.hMul 4 (instHAdd.hAdd n 1)) 2)) 2)))
            (abs (LocalDef007 x y)))
          (instHMul.hMul
            (instHPow.hPow (LocalDef008 fp.u (instHSub.hSub (instHMul.hMul 4 (instHAdd.hAdd n 1)) 2)) K)
            (LocalDef006 x y)))
```

## Fully explicit elaborated target type

```lean
∀ (fp : LocalDef002) (n K : Nat)
  (x y :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real)
  (hK : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) K)
  (hsmall :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 8)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (LocalDef004
          (LocalDef001 (LocalDef003 fp))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@LocalDef005 fp n K x y)
        (@LocalDef007 n x y)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (LocalDef004
            (LocalDef001 (LocalDef003 fp)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (LocalDef008
                (LocalDef004
                  (LocalDef001
                    (LocalDef003 fp)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@abs.{0} Real Real.lattice Real.instAddGroup (@LocalDef007 n x y)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (LocalDef008
            (LocalDef004
              (LocalDef001 (LocalDef003 fp)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          K)
        (@LocalDef006 n x y)))
```

## Complete semantic dependency inventory

Account for every dependency ID in the translation output. Names are not definitions;
use the supplied types and bodies to determine their exact meanings.

### D001: `LocalDef001`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
LocalDef009 → LocalDef011
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D002: `LocalDef002`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Type
```

### D003: `LocalDef003`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
LocalDef002 → LocalDef009
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D004: `LocalDef004`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
LocalDef011 → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D005: `LocalDef005`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
LocalDef002 →
  {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} K x y => LocalDef013 fp.toErrorFreeAddModel (instHSub.hSub K 1) (LocalDef012 fp x y)
```

### D006: `LocalDef006`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (abs (x i)) (abs (y i))
```

### D007: `LocalDef007`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (x i) (y i)
```

### D008: `LocalDef008`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Real → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun u n => instHDiv.hDiv (instHMul.hMul n.cast u) (instHSub.hSub 1 (instHMul.hMul n.cast u))
```

### D009: `LocalDef009`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `inductive`
- Distance from target type: `2`

Type:

```lean
Type
```

### D010: `LocalDef010`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `2`

Type:

```lean
(toErrorFreeAddModel : LocalDef009) →
  (twoProduct : Real → Real → Prod Real Real) →
    (∀ (a b : Real), Eq (instHAdd.hAdd (twoProduct a b).fst (twoProduct a b).snd) (instHMul.hMul a b)) →
      (∀ (a b : Real),
          Real.instLE.le (abs (twoProduct a b).snd) (instHMul.hMul toErrorFreeAddModel.u (abs (instHMul.hMul a b)))) →
        LocalDef002
```

### D011: `LocalDef011`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `inductive`
- Distance from target type: `2`

Type:

```lean
Type
```

### D012: `LocalDef012`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
LocalDef002 →
  {n : Nat} →
    (Fin (instHAdd.hAdd n 1) → Real) →
      (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 n) 1) 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} x y j =>
  Fin.addCases (fun i => (fp.twoProduct (x i) (y i)).snd)
    (LocalDef021 fp.toErrorFreeAddModel fun i => (fp.twoProduct (x i) (y i)).fst) (Fin.cast ⋯ j)
```

### D013: `LocalDef013`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
LocalDef009 → {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} K v =>
  LocalDef020 fp.fl_add (instHAdd.hAdd n 1) (LocalDef019 fp (instHSub.hSub K 1) v)
```

### D014: `LocalDef014`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `constructor`
- Distance from target type: `3`

Type:

```lean
(toStandardAddModel : LocalDef011) →
  (twoSum : Real → Real → Prod Real Real) →
    (∀ (a b : Real), Eq (twoSum a b).fst (toStandardAddModel.fl_add a b)) →
      (∀ (a b : Real), Eq (instHAdd.hAdd (twoSum a b).fst (twoSum a b).snd) (instHAdd.hAdd a b)) →
        (∀ (a b : Real),
            Real.instLE.le (abs (twoSum a b).snd) (instHMul.hMul toStandardAddModel.u (abs (twoSum a b).fst))) →
          LocalDef009
```

### D015: `LocalDef015`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
LocalDef002 → Real → Real → Prod Real Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D016: `LocalDef016`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
LocalDef011 → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D017: `LocalDef017`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `constructor`
- Distance from target type: `3`

Type:

```lean
(u : Real) →
  Real.instLE.le 0 u →
    (fl_add : Real → Real → Real) →
      (∀ (x : Real), Eq (fl_add 0 x) x) →
        (∀ (x y : Real),
            Exists fun δ =>
              And (Real.instLE.le (abs δ) u)
                (Eq (fl_add x y) (instHMul.hMul (instHAdd.hAdd x y) (instHAdd.hAdd 1 δ)))) →
          LocalDef011
```

### D018: `LocalDef018`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ {n : Nat},
  Eq (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 n) 1) 1) (instHAdd.hAdd (instHAdd.hAdd n 1) (instHAdd.hAdd n 1))
```

### D019: `LocalDef019`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
LocalDef009 → {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} k v =>
  Nat.brecOn (motive := fun k => Fin (instHAdd.hAdd n 1) → Real) k fun k f =>
    LocalDef022
      (fun k => Nat.below (motive := fun k => Fin (instHAdd.hAdd n 1) → Real) k → Fin (instHAdd.hAdd n 1) → Real) k
      (fun _ x => v) (fun k x => LocalDef021 fp x.1) f
```

### D020: `LocalDef020`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
(Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun flAdd x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Real) x
    (fun x f x_2 =>
      LocalDef024 (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Real) x → Real) x
        x_2 (fun x x_3 => 0)
        (fun n v x => if h : Eq n 0 then v ⟨0, ⋯⟩ else flAdd (x.1 fun i => v i.castSucc) (v (Fin.last n))) f)
    x_1
```

### D021: `LocalDef021`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
LocalDef009 → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd n 1) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v i => Fin.lastCases (LocalDef026 fp v n ⋯) (LocalDef025 fp v) i
```

### D022: `LocalDef022`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
(motive : Nat → Sort u_1) → (k : Nat) → (Unit → motive 0) → ((k : Nat) → motive k.succ) → motive k
```

Definition body (one-level semantic boundary):

```lean
fun motive k h_1 h_2 => Nat.casesOn k (h_1 Unit.unit) fun n => h_2 n
```

### D023: `LocalDef023`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `theorem`
- Distance from target type: `4`

Type:

```lean
∀ (n : Nat), Eq n 0 → instLTNat.lt 0 (instHAdd.hAdd n 1)
```

### D024: `LocalDef024`

- Role: `local`
- Owner module: `LocalImport001`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      ((x : Fin 0 → Real) → motive 0 x) →
        ((n : Nat) → (v : Fin (instHAdd.hAdd n 1) → Real) → motive n.succ v) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D025: `LocalDef025`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
LocalDef009 → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v i => (fp.twoSum (LocalDef026 fp v i.val ⋯) (v ⟨instHAdd.hAdd i.val 1, ⋯⟩)).snd
```

### D026: `LocalDef026`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
LocalDef009 → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (k : Nat) → instLENat.le k n → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v k hk => Fin.foldl k (fun s i => (fp.twoSum s (v ⟨instHAdd.hAdd i.val 1, ⋯⟩)).fst) (v ⟨0, ⋯⟩)
```

### D027: `LocalDef027`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `abbrev`
- Distance from target type: `5`

Type:

```lean
LocalDef009 → Real → Real → Prod Real Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D028: `LocalDef028`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLENat.le i.val n
```

### D029: `LocalDef029`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLTNat.lt i.val.succ n.succ
```

### D030: `LocalDef030`

- Role: `local`
- Owner module: `LocalImport002`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (k : Nat), instLENat.le k n → ∀ (i : Fin k), instLTNat.lt i.val.succ n.succ
```

### D031: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Nat → Type
```

### D032: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HAdd α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HAdd α β γ] => self.1
```

### D033: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HMul α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HMul α β γ] => self.1
```

### D034: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HPow α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HPow α β γ] => self.1
```

### D035: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSub α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSub α β γ] => self.1
```

### D036: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → [self : LE α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LE α] => self.1
```

### D037: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{M : Type u_2} → [Monoid M] → Pow M Nat
```

Definition body (one-level semantic boundary):

```lean
fun {M} [inst : Monoid M] => { pow := fun x n => inst.npow n x }
```

### D038: `Nat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Type
```

### D039: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{R : Type u} → [NatCast R] → Nat → R
```

Definition body (one-level semantic boundary):

```lean
fun {R} [inst : NatCast R] => inst.natCast
```

### D040: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `1`

Type:

```lean
∀ (n : Nat) [NeZero n], (instHAdd.hAdd n 1).AtLeastTwo
```

### D041: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `1`

Type:

```lean
∀ {n : Nat}, NeZero (instHAdd.hAdd n 1)
```

### D042: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat α x] → α
```

Definition body (one-level semantic boundary):

```lean
fun α x [self : OfNat α x] => self.1
```

### D043: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → [One α] → OfNat α 1
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : One α] => { ofNat := inst.one }
```

### D044: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `1`

Type:

```lean
Type
```

### D045: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Add Real
```

Definition body (one-level semantic boundary):

```lean
{ add := Real.add✝ }
```

### D046: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
AddGroup Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D047: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
LE Real
```

Definition body (one-level semantic boundary):

```lean
{ le := Real.le✝ }
```

### D048: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Monoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D049: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Mul Real
```

Definition body (one-level semantic boundary):

```lean
{ mul := Real.mul✝ }
```

### D050: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
NatCast Real
```

Definition body (one-level semantic boundary):

```lean
{ natCast := fun n => { cauchy := n.cast } }
```

### D051: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
One Real
```

Definition body (one-level semantic boundary):

```lean
{ one := Real.one✝ }
```

### D052: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Sub Real
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun a b => instHAdd.hAdd a (Real.instNeg.neg b) }
```

### D053: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Lattice Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D054: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → [Lattice α] → [AddGroup α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Lattice α] [AddGroup α] a =>
  SemilatticeSup.toMax.max a (SubtractionMonoid.toSubNegZeroMonoid.toNegZeroClass.neg a)
```

### D055: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Add Nat
```

Definition body (one-level semantic boundary):

```lean
{ add := Nat.add }
```

### D056: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → [Add α] → HAdd α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Add α] => { hAdd := fun a b => inst.add a b }
```

### D057: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → [Mul α] → HMul α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Mul α] => { hMul := fun a b => inst.mul a b }
```

### D058: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow α β] → HPow α β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : Pow α β] => { hPow := fun a b => inst.pow a b }
```

### D059: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{α : Type u_1} → [Sub α] → HSub α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Sub α] => { hSub := fun a b => inst.sub a b }
```

### D060: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
LE Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D061: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Mul Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul }
```

### D062: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast R] → [n.AtLeastTwo] → OfNat R n
```

Definition body (one-level semantic boundary):

```lean
fun {R} {n} [NatCast R] [n.AtLeastTwo] => { ofNat := n.cast }
```

### D063: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
(n : Nat) → OfNat Nat n
```

Definition body (one-level semantic boundary):

```lean
fun n => { ofNat := n }
```

### D064: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
Sub Nat
```

Definition body (one-level semantic boundary):

```lean
{ sub := Nat.sub }
```

### D065: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`

Type:

```lean
{G : Type u} → [self : DivInvMonoid G] → Div G
```

Definition body (one-level semantic boundary):

```lean
fun G [self : DivInvMonoid G] => self.3
```

### D066: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
(n : Nat) → Fintype (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n => { elems := { val := Multiset.ofList (List.finRange n), nodup := ⋯ }, complete := ⋯ }
```

### D067: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid M] → Finset ι → (ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [AddCommMonoid M] s f => (Multiset.map f s.val).sum
```

### D068: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{α : Type u_1} → [Fintype α] → Finset α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Fintype α] => inst.elems
```

### D069: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HDiv α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HDiv α β γ] => self.1
```

### D070: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
AddCommMonoid Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D071: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
DivInvMonoid Real
```

Definition body (one-level semantic boundary):

```lean
{ toMonoid := Real.instMonoid, toInv := Real.instInv, div := DivInvMonoid.div',
  div_eq_mul_inv := Real.instDivInvMonoid._proof_1, zpow := zpowRec, zpow_zero' := Real.instDivInvMonoid._proof_2,
  zpow_succ' := Real.instDivInvMonoid._proof_3, zpow_neg' := Real.instDivInvMonoid._proof_4 }
```

### D072: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{α : Type u_1} → [Div α] → HDiv α α α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Div α] => { hDiv := fun a b => inst.div a b }
```

### D073: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D074: `Fin.addCases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
{m n : Nat} →
  {motive : Fin (instHAdd.hAdd m n) → Sort u} →
    ((i : Fin m) → motive (Fin.castAdd n i)) →
      ((i : Fin n) → motive (Fin.natAdd m i)) → (i : Fin (instHAdd.hAdd m n)) → motive i
```

Definition body (one-level semantic boundary):

```lean
fun {m n} {motive} left right i =>
  if hi : instLTNat.lt i.val m then Eq.rec (left (i.castLT hi)) ⋯ else Eq.rec (right (Fin.subNat m (Fin.cast ⋯ i) ⋯)) ⋯
```

### D075: `Fin.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
{n m : Nat} → Eq n m → Fin n → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} eq i => ⟨i.val, ⋯⟩
```

### D076: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`

Type:

```lean
Type u → Type v → Type (max u v)
```

### D077: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D078: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D079: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`

Type:

```lean
Prop → Prop → Prop
```

### D080: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `4`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

### D081: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
{n : Nat} → Fin n → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => Fin.castAdd 1
```

### D082: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
(n : Nat) → Fin (instHAdd.hAdd n 1)
```

Definition body (one-level semantic boundary):

```lean
fun n => ⟨n, ⋯⟩
```

### D083: `Fin.lastCases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive (Fin.last n) → ((i : Fin n) → motive i.castSucc) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} last cast i => Fin.reverseInduction last (fun i x => cast i) i
```

### D084: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

### D085: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
{motive : Nat → Sort u} → Nat → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t => Nat.rec PUnit (fun n n_ih => PProd (motive n) n_ih) t
```

### D086: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → ((t : Nat) → Nat.below t → motive t) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t F_1 => (Nat.brecOn.go t F_1).1
```

### D087: `Nat.le_refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `4`

Type:

```lean
∀ (n : Nat), instLENat.le n n
```

### D088: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`

Type:

```lean
Nat → Nat
```

### D089: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
Prop → Prop
```

Definition body (one-level semantic boundary):

```lean
fun a => a → False
```

### D090: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
Zero Real
```

Definition body (one-level semantic boundary):

```lean
{ zero := Real.zero✝ }
```

### D091: `Unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
Type
```

Definition body (one-level semantic boundary):

```lean
PUnit
```

### D092: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
{α : Type u_1} → [Zero α] → OfNat α 0
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : Zero α] => { ofNat := inst.zero }
```

### D093: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (c → α) → (Not c → α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h e t
```

### D094: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`

Type:

```lean
DecidableEq Nat
```

Definition body (one-level semantic boundary):

```lean
Nat.decEq
```

### D095: `Fin.foldl`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Fold`
- Declaration kind: `def`
- Distance from target type: `5`

Type:

```lean
{α : Sort u_1} → (n : Nat) → (α → Fin n → α) → α → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} n f init => Fin.foldl.loop✝ n f init 0
```

### D096: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D097: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`

Type:

```lean
{α : Type u} → [self : LT α] → α → α → Prop
```

Definition body (one-level semantic boundary):

```lean
fun α [self : LT α] => self.1
```

### D098: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`

Type:

```lean
{motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive n.succ) → motive t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} t zero succ => Nat.rec zero (fun n n_ih => succ n) t
```

### D099: `Nat.succ_pos`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ (n : Nat), instLTNat.lt 0 n.succ
```

### D100: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `5`

Type:

```lean
Nat
```

### D101: `Unit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`

Type:

```lean
Unit
```

Definition body (one-level semantic boundary):

```lean
PUnit.unit
```

### D102: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`

Type:

```lean
LT Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
```
