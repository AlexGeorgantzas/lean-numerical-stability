# Declaration dossier for P02-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y
```

## Elaborated target type

```lean
∀ (fp : HighamBench.ErrorFreeDotModel) (n K : Nat) (x y : Fin (instHAdd.hAdd n 1) → Real),
  instLENat.le 3 K →
    Real.instLE.le (instHMul.hMul (instHMul.hMul 8 (instHAdd.hAdd n 1).cast) fp.u) 1 →
      Real.instLE.le (abs (instHSub.hSub (HighamBench.dotK fp K x y) (HighamBench.exactDot x y)))
        (instHAdd.hAdd
          (instHMul.hMul
            (instHAdd.hAdd fp.u
              (instHMul.hMul 2
                (instHPow.hPow (HighamBench.gamma fp.u (instHSub.hSub (instHMul.hMul 4 (instHAdd.hAdd n 1)) 2)) 2)))
            (abs (HighamBench.exactDot x y)))
          (instHMul.hMul
            (instHPow.hPow (HighamBench.gamma fp.u (instHSub.hSub (instHMul.hMul 4 (instHAdd.hAdd n 1)) 2)) K)
            (HighamBench.dotMagnitude x y)))
```

## Fully explicit elaborated target type

```lean
∀ (fp : HighamBench.ErrorFreeDotModel) (n K : Nat)
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
        (HighamBench.StandardAddModel.u
          (HighamBench.ErrorFreeAddModel.toStandardAddModel (HighamBench.ErrorFreeDotModel.toErrorFreeAddModel fp))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@HighamBench.dotK fp n K x y)
        (@HighamBench.exactDot n x y)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (HighamBench.StandardAddModel.u
            (HighamBench.ErrorFreeAddModel.toStandardAddModel (HighamBench.ErrorFreeDotModel.toErrorFreeAddModel fp)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
              (HighamBench.gamma
                (HighamBench.StandardAddModel.u
                  (HighamBench.ErrorFreeAddModel.toStandardAddModel
                    (HighamBench.ErrorFreeDotModel.toErrorFreeAddModel fp)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@abs.{0} Real Real.lattice Real.instAddGroup (@HighamBench.exactDot n x y)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
          (HighamBench.gamma
            (HighamBench.StandardAddModel.u
              (HighamBench.ErrorFreeAddModel.toStandardAddModel (HighamBench.ErrorFreeDotModel.toErrorFreeAddModel fp)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          K)
        (@HighamBench.dotMagnitude n x y)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P02Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P02Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.ErrorFreeAddModel.toStandardAddModel`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
HighamBench.ErrorFreeAddModel → HighamBench.StandardAddModel
```

Fully explicit type:

```lean
(self : HighamBench.ErrorFreeAddModel) → HighamBench.StandardAddModel
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D002: `HighamBench.ErrorFreeDotModel`

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

### D003: `HighamBench.ErrorFreeDotModel.toErrorFreeAddModel`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`

Type:

```lean
HighamBench.ErrorFreeDotModel → HighamBench.ErrorFreeAddModel
```

Fully explicit type:

```lean
(self : HighamBench.ErrorFreeDotModel) → HighamBench.ErrorFreeAddModel
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D004: `HighamBench.StandardAddModel.u`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `1`

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

### D005: `HighamBench.dotK`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
HighamBench.ErrorFreeDotModel →
  {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeDotModel) →
  {n : Nat} →
    (K : Nat) →
      (x y :
          Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Real) →
        Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} K x y => HighamBench.sumK fp.toErrorFreeAddModel (instHSub.hSub K 1) (HighamBench.dotKTransform fp x y)
```

### D006: `HighamBench.dotMagnitude`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (x y :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (abs (x i)) (abs (y i))
```

### D007: `HighamBench.exactDot`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `1`

Type:

```lean
{n : Nat} → (Fin (instHAdd.hAdd n 1) → Real) → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (x y :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real) →
    Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (x i) (y i)
```

### D008: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `1`

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

### D009: `HighamBench.ErrorFreeAddModel`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D010: `HighamBench.ErrorFreeDotModel.mk`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`

Type:

```lean
(toErrorFreeAddModel : HighamBench.ErrorFreeAddModel) →
  (twoProduct : Real → Real → Prod Real Real) →
    (∀ (a b : Real), Eq (instHAdd.hAdd (twoProduct a b).fst (twoProduct a b).snd) (instHMul.hMul a b)) →
      (∀ (a b : Real),
          Real.instLE.le (abs (twoProduct a b).snd) (instHMul.hMul toErrorFreeAddModel.u (abs (instHMul.hMul a b)))) →
        HighamBench.ErrorFreeDotModel
```

Fully explicit type:

```lean
(toErrorFreeAddModel : HighamBench.ErrorFreeAddModel) →
  (twoProduct : Real → Real → Prod.{0, 0} Real Real) →
    (twoProduct_exact :
        ∀ (a b : Real),
          @Eq.{1} Real
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Prod.fst.{0, 0} Real Real (twoProduct a b)) (@Prod.snd.{0, 0} Real Real (twoProduct a b)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a b)) →
      (twoProduct_low_le_exact :
          ∀ (a b : Real),
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup (@Prod.snd.{0, 0} Real Real (twoProduct a b)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (HighamBench.StandardAddModel.u (HighamBench.ErrorFreeAddModel.toStandardAddModel toErrorFreeAddModel))
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a b)))) →
        HighamBench.ErrorFreeDotModel
```

### D011: `HighamBench.StandardAddModel`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `inductive`
- Distance from target type: `2`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D012: `HighamBench.dotKTransform`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
HighamBench.ErrorFreeDotModel →
  {n : Nat} →
    (Fin (instHAdd.hAdd n 1) → Real) →
      (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 n) 1) 1) → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeDotModel) →
  {n : Nat} →
    (x y :
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real) →
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} x y j =>
  Fin.addCases (fun i => (fp.twoProduct (x i) (y i)).snd)
    (HighamBench.vecSum fp.toErrorFreeAddModel fun i => (fp.twoProduct (x i) (y i)).fst) (Fin.cast ⋯ j)
```

### D013: `HighamBench.sumK`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `2`

Type:

```lean
HighamBench.ErrorFreeAddModel → {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeAddModel) →
  {n : Nat} →
    (K : Nat) →
      (v :
          Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Real) →
        Real
```

Definition body (one-level semantic boundary):

```lean
fun fp {n} K v =>
  HighamBench.recursiveSum fp.fl_add (instHAdd.hAdd n 1) (HighamBench.iteratedVecSum fp (instHSub.hSub K 1) v)
```

### D014: `HighamBench.ErrorFreeAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`

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

### D015: `HighamBench.ErrorFreeDotModel.twoProduct`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`

Type:

```lean
HighamBench.ErrorFreeDotModel → Real → Real → Prod Real Real
```

Fully explicit type:

```lean
(self : HighamBench.ErrorFreeDotModel) → Real → Real → Prod.{0, 0} Real Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D016: `HighamBench.StandardAddModel.fl_add`

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

### D017: `HighamBench.StandardAddModel.mk`

- Role: `local`
- Owner module: `HighamBench.Core`
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

### D018: `HighamBench.dotKTransform._proof_2`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `3`

Type:

```lean
∀ {n : Nat},
  Eq (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 n) 1) 1) (instHAdd.hAdd (instHAdd.hAdd n 1) (instHAdd.hAdd n 1))
```

Fully explicit type:

```lean
∀ {n : Nat},
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

### D019: `HighamBench.iteratedVecSum`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
HighamBench.ErrorFreeAddModel → {n : Nat} → Nat → (Fin (instHAdd.hAdd n 1) → Real) → Fin (instHAdd.hAdd n 1) → Real
```

Fully explicit type:

```lean
(fp : HighamBench.ErrorFreeAddModel) →
  {n : Nat} →
    (k : Nat) →
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
fun fp {n} k v =>
  Nat.brecOn (motive := fun k => Fin (instHAdd.hAdd n 1) → Real) k fun k f =>
    HighamBench.iteratedVecSum.match_1
      (fun k => Nat.below (motive := fun k => Fin (instHAdd.hAdd n 1) → Real) k → Fin (instHAdd.hAdd n 1) → Real) k
      (fun _ x => v) (fun k x => HighamBench.vecSum fp x.1) f
```

### D020: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `3`

Type:

```lean
(Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
(flAdd : Real → Real → Real) → (n : Nat) → (Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun flAdd x x_1 =>
  Nat.brecOn (motive := fun x => (Fin x → Real) → Real) x
    (fun x f x_2 =>
      HighamBench.recursiveSum.match_1 (fun x x_3 => Nat.below (motive := fun x => (Fin x → Real) → Real) x → Real) x
        x_2 (fun x x_3 => 0)
        (fun n v x => if h : Eq n 0 then v ⟨0, ⋯⟩ else flAdd (x.1 fun i => v i.castSucc) (v (Fin.last n))) f)
    x_1
```

### D021: `HighamBench.vecSum`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `3`

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

### D022: `HighamBench.iteratedVecSum.match_1`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `4`

Type:

```lean
(motive : Nat → Sort u_1) → (k : Nat) → (Unit → motive 0) → ((k : Nat) → motive k.succ) → motive k
```

Fully explicit type:

```lean
(motive : Nat → Sort u_1) →
  (k : Nat) →
    (h_1 : (a : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (k : Nat) → motive (Nat.succ k)) → motive k
```

Definition body (one-level semantic boundary):

```lean
fun motive k h_1 h_2 => Nat.casesOn k (h_1 Unit.unit) fun n => h_2 n
```

### D023: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Distance from target type: `4`

Type:

```lean
∀ (n : Nat), Eq n 0 → instLTNat.lt 0 (instHAdd.hAdd n 1)
```

Fully explicit type:

```lean
∀ (n : Nat) (h : @Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D024: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
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

Fully explicit type:

```lean
(motive : (x : Nat) → (Fin x → Real) → Sort u_1) →
  (x : Nat) →
    (x_1 : Fin x → Real) →
      (h_1 :
          (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → Real) →
            motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
        (h_2 :
            (n : Nat) →
              (v :
                  Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Real) →
                motive (Nat.succ n) v) →
          motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun motive x x_1 h_1 h_2 =>
  Nat.casesOn (motive := fun x => (x_2 : Fin x → Real) → motive x x_2) x (fun x => h_1 x) (fun n x => h_2 n x) x_1
```

### D025: `HighamBench.twoSumCorrection`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `4`

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

### D026: `HighamBench.twoSumPrefix`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `def`
- Distance from target type: `4`

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

### D027: `HighamBench.ErrorFreeAddModel.twoSum`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`

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

### D028: `HighamBench.twoSumCorrection._proof_1`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLENat.le i.val n
```

Fully explicit type:

```lean
∀ {n : Nat} (i : Fin n), @LE.le.{0} Nat instLENat (@Fin.val n i) n
```

### D029: `HighamBench.twoSumCorrection._proof_2`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (i : Fin n), instLTNat.lt i.val.succ n.succ
```

Fully explicit type:

```lean
∀ {n : Nat} (i : Fin n), @LT.lt.{0} Nat instLTNat (Nat.succ (@Fin.val n i)) (Nat.succ n)
```

### D030: `HighamBench.twoSumPrefix._proof_1`

- Role: `local`
- Owner module: `HighamBench.P02Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`

Type:

```lean
∀ {n : Nat} (k : Nat), instLENat.le k n → ∀ (i : Fin k), instLTNat.lt i.val.succ n.succ
```

Fully explicit type:

```lean
∀ {n : Nat} (k : Nat) (hk : @LE.le.{0} Nat instLENat k n) (i : Fin k),
  @LT.lt.{0} Nat instLTNat (Nat.succ (@Fin.val k i)) (Nat.succ n)
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

Fully explicit type:

```lean
(n : Nat) → Type
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HAdd.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HMul.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HPow.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSub.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
{α : Type u} → [self : LE.{u} α] → α → α → Prop
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

Fully explicit type:

```lean
{M : Type u_2} → [Monoid.{u_2} M] → Pow.{u_2, 0} M Nat
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

Fully explicit type:

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

Fully explicit type:

```lean
{R : Type u} → [NatCast.{u} R] → Nat → R
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

Fully explicit type:

```lean
∀ (n : Nat) [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n],
  Nat.AtLeastTwo
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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

Fully explicit type:

```lean
∀ {n : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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

Fully explicit type:

```lean
{α : Type u} → (x : Nat) → [self : OfNat.{u} α x] → α
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

Fully explicit type:

```lean
{α : Type u_1} → [One.{u_1} α] → OfNat.{u_1} α (nat_lit 1)
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

Fully explicit type:

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

Fully explicit type:

```lean
Add.{0} Real
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

Fully explicit type:

```lean
AddGroup.{0} Real
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

Fully explicit type:

```lean
LE.{0} Real
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

Fully explicit type:

```lean
Monoid.{0} Real
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

Fully explicit type:

```lean
Mul.{0} Real
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

Fully explicit type:

```lean
NatCast.{0} Real
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

Fully explicit type:

```lean
One.{0} Real
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

Fully explicit type:

```lean
Sub.{0} Real
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

Fully explicit type:

```lean
Lattice.{0} Real
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

Fully explicit type:

```lean
{α : Type u_1} → [Lattice.{u_1} α] → [AddGroup.{u_1} α] → (a : α) → α
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

Fully explicit type:

```lean
Add.{0} Nat
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

Fully explicit type:

```lean
{α : Type u_1} → [Add.{u_1} α] → HAdd.{u_1, u_1, u_1} α α α
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

Fully explicit type:

```lean
{α : Type u_1} → [Mul.{u_1} α] → HMul.{u_1, u_1, u_1} α α α
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

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [Pow.{u_1, u_2} α β] → HPow.{u_1, u_2, u_1} α β α
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

Fully explicit type:

```lean
{α : Type u_1} → [Sub.{u_1} α] → HSub.{u_1, u_1, u_1} α α α
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

Fully explicit type:

```lean
LE.{0} Nat
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

Fully explicit type:

```lean
Mul.{0} Nat
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

Fully explicit type:

```lean
{R : Type u_1} → {n : Nat} → [NatCast.{u_1} R] → [Nat.AtLeastTwo n] → OfNat.{u_1} R n
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

Fully explicit type:

```lean
(n : Nat) → OfNat.{0} Nat n
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

Fully explicit type:

```lean
Sub.{0} Nat
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

Fully explicit type:

```lean
{G : Type u} → [self : DivInvMonoid.{u} G] → Div.{u} G
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

Fully explicit type:

```lean
(n : Nat) → Fintype.{0} (Fin n)
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

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [AddCommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
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

Fully explicit type:

```lean
{α : Type u_1} → [Fintype.{u_1} α] → Finset.{u_1} α
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HDiv.{u, v, w} α β γ] → α → β → γ
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

Fully explicit type:

```lean
AddCommMonoid.{0} Real
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

### D072: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`

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

### D073: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

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

Fully explicit type:

```lean
{m n : Nat} →
  {motive : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n) → Sort u} →
    (left : (i : Fin m) → motive (@Fin.castAdd m n i)) →
      (right : (i : Fin n) → motive (@Fin.natAdd n m i)) →
        (i : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)) → motive i
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

Fully explicit type:

```lean
{n m : Nat} → (eq : @Eq.{1} Nat n m) → (i : Fin n) → Fin m
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

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → α
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

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (self : Prod.{u, v} α β) → β
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

Fully explicit type:

```lean
(a b : Prop) → Prop
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

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Prop
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

Fully explicit type:

```lean
{n : Nat} →
  Fin n →
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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

Fully explicit type:

```lean
(n : Nat) →
  Fin
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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

### D084: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
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

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → Sort (max 1 u)
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

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} → (t : Nat) → (F_1 : (t : Nat) → (f : @Nat.below.{u} motive t) → motive t) → motive t
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

Fully explicit type:

```lean
∀ (n : Nat), @LE.le.{0} Nat instLENat n n
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

Fully explicit type:

```lean
(n : Nat) → Nat
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

Fully explicit type:

```lean
(a : Prop) → Prop
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

Fully explicit type:

```lean
Zero.{0} Real
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

Fully explicit type:

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

Fully explicit type:

```lean
{α : Type u_1} → [Zero.{u_1} α] → OfNat.{u_1} α (nat_lit 0)
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

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t : c → α) → (e : Not c → α) → α
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

Fully explicit type:

```lean
DecidableEq.{1} Nat
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

Fully explicit type:

```lean
{α : Sort u_1} → (n : Nat) → (f : α → Fin n → α) → (init : α) → α
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

Fully explicit type:

```lean
{n : Nat} → (self : Fin n) → Nat
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

Fully explicit type:

```lean
{α : Type u} → [self : LT.{u} α] → α → α → Prop
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

Fully explicit type:

```lean
{motive : (t : Nat) → Sort u} →
  (t : Nat) → (zero : motive Nat.zero) → (succ : (n : Nat) → motive (Nat.succ n)) → motive t
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

Fully explicit type:

```lean
∀ (n : Nat), @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (Nat.succ n)
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

Fully explicit type:

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

Fully explicit type:

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

Fully explicit type:

```lean
LT.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ lt := Nat.lt }
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
