# Declaration dossier for P02-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p02_t1_vecSum_preserves_sum
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ) :
    ∑ i : Fin (n + 1), vecSum fp v i = ∑ i : Fin (n + 1), v i
```

## Elaborated target type

```lean
∀ (fp : HighamBench.ErrorFreeAddModel) (n : Nat) (v : Fin (instHAdd.hAdd n 1) → Real),
  Eq (Finset.univ.sum fun i => HighamBench.vecSum fp v i) (Finset.univ.sum fun i => v i)
```

## Fully explicit elaborated target type

```lean
∀ (fp : HighamBench.ErrorFreeAddModel) (n : Nat)
  (v :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid
      (@Finset.univ.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      fun
        (i :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @HighamBench.vecSum fp n v i)
    (@Finset.sum.{0, 0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid
      (@Finset.univ.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Fin.fintype
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      fun
        (i :
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      v i)
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P02Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P02Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.ErrorFreeAddModel`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
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

### D002: `HighamBench.vecSum`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
HighamBench.ErrorFreeAddModel → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeAddModel) →
  {n : Nat} →
    (v :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v i => Fin.lastCases (HighamBench.twoSumPrefix fp v n ⋯) (HighamBench.twoSumCorrection fp v) i
```

### D003: `HighamBench.ErrorFreeAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`

Type:

```lean
(toStandardAddModel : HighamBench.StandardAddModel) →
  (twoSum : Real → Real → Prod Real Real) →
    (∀ (a b : Real), Eq (twoSum a b).fst (toStandardAddModel.fl_add a b)) →
      (∀ (a b : Real), Eq (instHAdd.hAdd (twoSum a b).fst (twoSum a b).snd) (instHAdd.hAdd a b)) →
        (∀ (a b : Real),
            Real.instLE.le (abs (twoSum a b).snd) (instHMul.hMul toStandardAddModel.u (abs (twoSum a b).fst))) →
          HighamBench.ErrorFreeAddModel
```

Fully explicit type:

```lean
(toStandardAddModel : HighamBench.StandardAddModel) →
  (twoSum : Real → Real → Prod.{0, 0} Real Real) →
    (twoSum_high :
        ∀ (a b : Real),
          @Eq.{1} Real (@Prod.fst.{0, 0} Real Real (twoSum a b))
            (HighamBench.StandardAddModel.fl_add toStandardAddModel a b)) →
      (twoSum_exact :
          ∀ (a b : Real),
            @Eq.{1} Real
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@Prod.fst.{0, 0} Real Real (twoSum a b)) (@Prod.snd.{0, 0} Real Real (twoSum a b)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a b)) →
        (twoSum_low_le :
            ∀ (a b : Real),
              @LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup (@Prod.snd.{0, 0} Real Real (twoSum a b)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (HighamBench.StandardAddModel.u toStandardAddModel)
                  (@abs.{0} Real Real.lattice Real.instAddGroup (@Prod.fst.{0, 0} Real Real (twoSum a b))))) →
          HighamBench.ErrorFreeAddModel
```

### D004: `HighamBench.twoSumCorrection`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
HighamBench.ErrorFreeAddModel → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → Fin n → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeAddModel) →
  {n : Nat} →
    (v :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
      (i : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v i => (fp.twoSum (HighamBench.twoSumPrefix fp v i.val ⋯) (v ⟨instHAdd.hAdd i.val 1, ⋯⟩)).snd
```

### D005: `HighamBench.twoSumPrefix`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
HighamBench.ErrorFreeAddModel → {n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (k : Nat) → instLENat.le k n → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeAddModel) →
  {n : Nat} →
    (v :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
      (k : Nat) → (hk : @LE.le.{0} Nat instLENat k n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} v k hk => Fin.foldl k (fun s i => (fp.twoSum s (v ⟨instHAdd.hAdd i.val 1, ⋯⟩)).fst) (v ⟨0, ⋯⟩)
```

### D006: `HighamBench.ErrorFreeAddModel.twoSum`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
HighamBench.ErrorFreeAddModel → Real → Real → Prod Real Real
```

Fully explicit type:

```lean
(self : HighamBench.ErrorFreeAddModel) → Real → Real → Prod.{0, 0} Real Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D007: `HighamBench.StandardAddModel`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `inductive`
- Distance from target type: `3`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D008: `HighamBench.StandardAddModel.fl_add`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
HighamBench.StandardAddModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.StandardAddModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D009: `HighamBench.StandardAddModel.u`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
HighamBench.StandardAddModel → Real
```

Fully explicit type:

```lean
(self : HighamBench.StandardAddModel) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D010: `HighamBench.twoSumCorrection._proof_1`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLENat.le i.val n
```

Fully explicit type:

```lean
∀ {n : Nat} (i : Fin n), @LE.le.{0} Nat instLENat (@Fin.val n i) n
```

### D011: `HighamBench.twoSumCorrection._proof_2`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLTNat.lt i.val.succ n.succ
```

Fully explicit type:

```lean
∀ {n : Nat} (i : Fin n), @LT.lt.{0} Nat instLTNat (Nat.succ (@Fin.val n i)) (Nat.succ n)
```

### D012: `HighamBench.twoSumPrefix._proof_1`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ {n : Nat} (k : Nat), instLENat.le k n → ∀ (i : Fin k), instLTNat.lt i.val.succ n.succ
```

Fully explicit type:

```lean
∀ {n : Nat} (k : Nat) (hk : @LE.le.{0} Nat instLENat k n) (i : Fin k),
  @LT.lt.{0} Nat instLTNat (Nat.succ (@Fin.val k i)) (Nat.succ n)
```

### D013: `HighamBench.StandardAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `constructor`
- Distance from target type: `4`

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
          HighamBench.StandardAddModel
```

Fully explicit type:

```lean
(u : Real) →
  (u_nonneg :
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u) →
    (fl_add : Real → Real → Real) →
      (fl_add_zero :
          ∀ (x : Real),
            @Eq.{1} Real (fl_add (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x) x) →
        (model_add :
            ∀ (x y : Real),
              @Exists.{1} Real fun (δ : Real) =>
                And (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup δ) u)
                  (@Eq.{1} Real (fl_add x y)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) δ)))) →
          HighamBench.StandardAddModel
```

### D014: `Eq`

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

### D015: `Fin`

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

### D016: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D017: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D018: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D019: `HAdd.hAdd`

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

### D020: `Nat`

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

### D021: `OfNat.ofNat`

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

### D022: `Real`

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

### D023: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D024: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D025: `instHAdd`

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

### D026: `instOfNatNat`

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

### D027: `Fin.lastCases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive (Fin.last n) → ((i : Fin n) → motive i.castSucc) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Fully explicit type:

```lean
{n : Nat} →
  {motive :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Sort u_1} →
    (last : motive (Fin.last n)) →
      (cast : (i : Fin n) → motive (@Fin.castSucc n i)) →
        (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} last cast i => Fin.reverseInduction last (fun i x => cast i) i
```

### D028: `Nat.le_refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `2`

Type:

```lean
∀ (n : Nat), instLENat.le n n
```

Fully explicit type:

```lean
∀ (n : Nat), @LE.le.{0} Nat instLENat n n
```

### D029: `Fin.foldl`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Fold`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
{α : Sort u_1} → (n : Nat) → (α → Fin n → α) → α → α
```

Fully explicit type:

```lean
{α : Sort u_1} → (n : Nat) → (f : α → Fin n → α) → (init : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} n f init => Fin.foldl.loop✝ n f init 0
```

### D030: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D031: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
{n : Nat} → Fin n → Nat
```

Fully explicit type:

```lean
{n : Nat} → (self : Fin n) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D032: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

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

### D033: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

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

### D034: `Nat.succ_pos`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ (n : Nat), instLTNat.lt 0 n.succ
```

Fully explicit type:

```lean
∀ (n : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.succ n)
```

### D035: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D036: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → α
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → α
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.1
```

### D037: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
{α : Type u} → {β : Type v} → Prod α β → β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → β
```

Definition body (one-level semantic boundary):

```lean
fun α β self => self.2
```

### D038: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D039: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D040: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D041: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D042: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D043: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D044: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D045: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
LE Nat
```

Fully explicit type:

```lean
LE.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ le := Nat.le }
```

### D046: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`

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

### D047: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D048: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`

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

### D049: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D050: `Exists`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `5`

Type:

```lean
{α : Sort u} → (α → Prop) → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
```

### D051: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `5`

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

### D052: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`

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

### D053: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`

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

### D054: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `5`

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

### `HighamBench.P02Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P02Definitions.lean`
SHA-256: `803efe47eb37140c04ed8dad9fcdfe8470d0527aaedf9c60ff9333441ad5136b`

```lean
import HighamBench.Core

/-!
# HighamBench P02 definitions

This file contains only the error-free transformations and algorithms needed
for P02, the Ogita--Rump--Oishi paper on accurate sums and dot products.
-/

namespace HighamBench

open scoped BigOperators

/-! ## Ogita--Rump--Oishi error-free transformations

The P02 tasks use only the mathematical contracts of `TwoSum` and
`TwoProduct` that the paper establishes before analyzing `VecSum`, `Sum2`, and
`DotK`. Keeping those contracts abstract avoids building IEEE-754 machinery
into the fixed statements and gives conditions N and L the same small model.
-/

/-- A standard rounded-addition model equipped with an error-free `TwoSum`.

The first component is the rounded sum. The two components add to the exact
real sum, and the low component obeys the residual estimate used in Lemma 4.2
of Ogita--Rump--Oishi (2005). -/
structure ErrorFreeAddModel extends StandardAddModel where
  twoSum : ℝ → ℝ → ℝ × ℝ
  twoSum_high :
    ∀ a b : ℝ, (twoSum a b).1 = fl_add a b
  twoSum_exact :
    ∀ a b : ℝ, (twoSum a b).1 + (twoSum a b).2 = a + b
  twoSum_low_le :
    ∀ a b : ℝ, |(twoSum a b).2| ≤ u * |(twoSum a b).1|

/-- Main value after `k` successive `TwoSum` operations, starting with the
first entry of a nonempty vector. -/
noncomputable def twoSumPrefix (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) : ℝ :=
  Fin.foldl k
    (fun s i =>
      (fp.twoSum s
        (v ⟨i.val + 1,
          Nat.succ_lt_succ (Nat.lt_of_lt_of_le i.isLt hk)⟩)).1)
    (v ⟨0, Nat.succ_pos n⟩)

/-- The low component emitted at step `i+1` of the `VecSum` cascade. -/
noncomputable def twoSumCorrection (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (fp.twoSum
    (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
    (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).2

/-- Algorithm 4.3 (`VecSum`): the `n` emitted low components followed by the
final high component. The input and output both have length `n+1`. -/
noncomputable def vecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases
    (twoSumPrefix fp v n (Nat.le_refl n))
    (twoSumCorrection fp v)

/-- Apply `VecSum` exactly `k` times. -/
noncomputable def iteratedVecSum (fp : ErrorFreeAddModel) {n : ℕ}
    (k : ℕ) (v : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  match k with
  | 0 => v
  | k + 1 => vecSum fp (iteratedVecSum fp k v)

/-- Algorithm 4.8 (`SumK`): apply `VecSum` `K-1` times and recursively sum the
result in working precision. -/
noncomputable def sumK (fp : ErrorFreeAddModel) {n : ℕ}
    (K : ℕ) (v : Fin (n + 1) → ℝ) : ℝ :=
  recursiveSum fp.fl_add (n + 1) (iteratedVecSum fp (K - 1) v)

/-- Algorithm 4.4 (`Sum2`), the `K = 2` instance of `SumK`. -/
noncomputable def sum2 (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp 2 v

/-- The no-multiplication-underflow contract used for the P02 `DotK` task.

The two product components add exactly to `a*b`, and the low component is at
most unit roundoff times the exact product. This is the minimal part of
Theorem 3.4 needed for the transformed-vector absolute-mass estimate. -/
structure ErrorFreeDotModel extends ErrorFreeAddModel where
  twoProduct : ℝ → ℝ → ℝ × ℝ
  twoProduct_exact :
    ∀ a b : ℝ, (twoProduct a b).1 + (twoProduct a b).2 = a * b
  twoProduct_low_le_exact :
    ∀ a b : ℝ, |(twoProduct a b).2| ≤ u * |a * b|

/-- Exact real dot product of two nonempty vectors. -/
noncomputable def exactDot {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), x i * y i

/-- Componentwise absolute mass `|x|ᵀ|y|` of a dot product. -/
noncomputable def dotMagnitude {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), |x i| * |y i|

/-- The length-`2*(n+1)` vector passed to `SumK` in Algorithm 5.10.

Its first half contains the low parts from `TwoProduct`; its second half is
`VecSum` applied to the product high parts, hence contains the addition lows
and the final high component. -/
noncomputable def dotKTransform (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) : Fin ((2 * n + 1) + 1) → ℝ :=
  fun j =>
    Fin.addCases
      (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).2)
      (vecSum fp.toErrorFreeAddModel
        (fun i : Fin (n + 1) => (fp.twoProduct (x i) (y i)).1))
      (Fin.cast (by omega) j)

/-- Algorithm 5.10 (`DotK`): transform the products and call `SumK` with
precision parameter `K-1`. -/
noncomputable def dotK (fp : ErrorFreeDotModel) {n : ℕ}
    (K : ℕ) (x y : Fin (n + 1) → ℝ) : ℝ :=
  sumK fp.toErrorFreeAddModel (K - 1) (dotKTransform fp x y)

end HighamBench
```
