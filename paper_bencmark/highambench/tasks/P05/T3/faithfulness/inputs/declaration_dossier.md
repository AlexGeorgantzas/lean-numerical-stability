# Declaration dossier for P05-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p05_t3_cholesky_backward_error
    {n : ℕ} (run : P05CholeskyRun n) :
    (∀ i j, i.val < j.val →
      |run.A i j - p05CholeskyThroughDot run.RHat i j| ≤
        ((i.val + 1 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat i j) ∧
    (∀ j,
      |run.A j j - p05CholeskyThroughDot run.RHat j j| ≤
        ((j.val + 2 : ℕ) : ℝ) * run.format.unitRoundoff *
          p05CholeskyThroughAbsDot run.RHat j j) ∧
    ∃ ΔA : Fin n → Fin n → ℝ,
      p05MatMul (p05Transpose run.RHat) run.RHat = run.A + ΔA ∧
      (∀ i j,
        |ΔA i j| ≤ ((i.val + 2 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j) ∧
      ∀ i j,
        |ΔA i j| ≤ ((n + 1 : ℕ) : ℝ) *
          run.format.unitRoundoff *
            p05AbsMatMul (p05Transpose run.RHat) run.RHat i j
```

## Elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P05CholeskyRun n),
  And
    (∀ (i j : Fin n),
      instLTNat.lt i.val j.val →
        Real.instLE.le (abs (instHSub.hSub (run.A i j) (HighamBench.p05CholeskyThroughDot run.RHat i j)))
          (instHMul.hMul (instHMul.hMul (instHAdd.hAdd i.val 1).cast run.format.unitRoundoff)
            (HighamBench.p05CholeskyThroughAbsDot run.RHat i j)))
    (And
      (∀ (j : Fin n),
        Real.instLE.le (abs (instHSub.hSub (run.A j j) (HighamBench.p05CholeskyThroughDot run.RHat j j)))
          (instHMul.hMul (instHMul.hMul (instHAdd.hAdd j.val 2).cast run.format.unitRoundoff)
            (HighamBench.p05CholeskyThroughAbsDot run.RHat j j)))
      (Exists fun ΔA =>
        And (Eq (HighamBench.p05MatMul (HighamBench.p05Transpose run.RHat) run.RHat) (instHAdd.hAdd run.A ΔA))
          (And
            (∀ (i j : Fin n),
              Real.instLE.le (abs (ΔA i j))
                (instHMul.hMul (instHMul.hMul (instHAdd.hAdd i.val 2).cast run.format.unitRoundoff)
                  (HighamBench.p05AbsMatMul (HighamBench.p05Transpose run.RHat) run.RHat i j)))
            (∀ (i j : Fin n),
              Real.instLE.le (abs (ΔA i j))
                (instHMul.hMul (instHMul.hMul (instHAdd.hAdd n 1).cast run.format.unitRoundoff)
                  (HighamBench.p05AbsMatMul (HighamBench.p05Transpose run.RHat) run.RHat i j))))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P05CholeskyRun n),
  And
    (∀ (i j : Fin n),
      @LT.lt.{0} Nat instLTNat (@Fin.val n i) (@Fin.val n j) →
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HighamBench.P05CholeskyRun.A n run i j)
              (@HighamBench.p05CholeskyThroughDot n (@HighamBench.P05CholeskyRun.RHat n run) i j)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff (@HighamBench.P05CholeskyRun.format n run)))
            (@HighamBench.p05CholeskyThroughAbsDot n (@HighamBench.P05CholeskyRun.RHat n run) i j)))
    (And
      (∀ (j : Fin n),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HighamBench.P05CholeskyRun.A n run j j)
              (@HighamBench.p05CholeskyThroughDot n (@HighamBench.P05CholeskyRun.RHat n run) j j)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n j)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff (@HighamBench.P05CholeskyRun.format n run)))
            (@HighamBench.p05CholeskyThroughAbsDot n (@HighamBench.P05CholeskyRun.RHat n run) j j)))
      (@Exists.{1} (Fin n → Fin n → Real) fun (ΔA : Fin n → Fin n → Real) =>
        And
          (@Eq.{1} (Fin n → Fin n → Real)
            (@HighamBench.p05MatMul n (@HighamBench.p05Transpose n (@HighamBench.P05CholeskyRun.RHat n run))
              (@HighamBench.P05CholeskyRun.RHat n run))
            (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real) (Fin n → Fin n → Real) (Fin n → Fin n → Real)
              (@instHAdd.{0} (Fin n → Fin n → Real)
                (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Fin n → Real) fun (i : Fin n) =>
                  @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
              (@HighamBench.P05CholeskyRun.A n run) ΔA))
          (And
            (∀ (i j : Fin n),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff (@HighamBench.P05CholeskyRun.format n run)))
                  (@HighamBench.p05AbsMatMul n (@HighamBench.p05Transpose n (@HighamBench.P05CholeskyRun.RHat n run))
                    (@HighamBench.P05CholeskyRun.RHat n run) i j)))
            (∀ (i j : Fin n),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (ΔA i j))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff (@HighamBench.P05CholeskyRun.format n run)))
                  (@HighamBench.p05AbsMatMul n (@HighamBench.p05Transpose n (@HighamBench.P05CholeskyRun.RHat n run))
                    (@HighamBench.P05CholeskyRun.RHat n run) i j))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P05Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P05Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P05CholeskyRun`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `41670d7043ab9bcf8acfca36686028e98c69d6357d62b880590e7cbd8eb55c8d`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.P05CholeskyRun.A`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `7b6294d9500295aa5a3260e8eeee822b2f5f231229e9f45047279e985156d087`

Type:

```lean
{n : Nat} → HighamBench.P05CholeskyRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P05CholeskyRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D003: `HighamBench.P05CholeskyRun.RHat`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `0c1f05486b2167643427ee6f27cd5944893c3f264bb42cd9042842874ebfc027`

Type:

```lean
{n : Nat} → HighamBench.P05CholeskyRun n → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P05CholeskyRun n) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.4
```

### D004: `HighamBench.P05CholeskyRun.format`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b9e045fdd52069fa1a058dfc506bf8a19285d59e5bd60dd454eade0dfa0314b4`

Type:

```lean
{n : Nat} → HighamBench.P05CholeskyRun n → HighamBench.P05FiniteRoundToNearestFormat
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P05CholeskyRun n) → HighamBench.P05FiniteRoundToNearestFormat
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D005: `HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3630b109f8786a050a03b7576d18b02aca25f370b7c3aeacef8aeb8f4eded07d`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → Real
```

Fully explicit type:

```lean
(self : HighamBench.P05FiniteRoundToNearestFormat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.12
```

### D006: `HighamBench.p05AbsMatMul`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fe75f4145e1b29dc797163b1c5e5bf58a54b99328abc1689fc23613d5d405671`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (abs (A i k)) (abs (B k j))
```

### D007: `HighamBench.p05CholeskyThroughAbsDot`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `698ba1b7f078e67d4e86f4014cffa6abbe7599d0cf04f876434ab0e3a585e695`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (R : Fin n → Fin n → Real) → (i j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R i j => instHAdd.hAdd (HighamBench.p05CholeskyPrefixAbsDot R i j) (instHMul.hMul (abs (R i i)) (abs (R i j)))
```

### D008: `HighamBench.p05CholeskyThroughDot`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7800d17cec05713eec46b0653f4c12ef894031fbde83299b16ca6b2b61d35a9c`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (R : Fin n → Fin n → Real) → (i j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R i j => instHAdd.hAdd (HighamBench.p05CholeskyPrefixDot R i j) (instHMul.hMul (R i i) (R i j))
```

### D009: `HighamBench.p05MatMul`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `8b658624127af1765d1831514845fbf3705f949e157d27c75ca6a03e4bd9cf19`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A B : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D010: `HighamBench.p05Transpose`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c98072df9e9b350096ec63ce7329d663300c9ad2c7358ac5d2f8a729a34d3102`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A i j => A j i
```

### D011: `HighamBench.P05CholeskyRun.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `049ec0731bbbbc0b1e863f13ea059e6abe25208792940eec06a9adbdcb5c834a`

Type:

```lean
{n : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    instLTNat.lt 0 n →
      (A RHat : Fin n → Fin n → Real) →
        (∀ (i j : Fin n), format.representable (A i j)) →
          (∀ (i j : Fin n), format.representable (RHat i j)) →
            (∀ (i j : Fin n), Eq (A i j) (A j i)) →
              (∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (RHat i j) 0) →
                ((i j : Fin n) → instLTNat.lt i.val j.val → HighamBench.P05CholeskyOffDiagonalEntry format A RHat i j) →
                  ((j : Fin n) → HighamBench.P05CholeskyDiagonalEntry format A RHat j) → HighamBench.P05CholeskyRun n
```

Fully explicit type:

```lean
{n : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
      (A RHat : Fin n → Fin n → Real) →
        (A_representable : ∀ (i j : Fin n), HighamBench.P05FiniteRoundToNearestFormat.representable format (A i j)) →
          (RHat_representable :
              ∀ (i j : Fin n), HighamBench.P05FiniteRoundToNearestFormat.representable format (RHat i j)) →
            (A_symmetric : ∀ (i j : Fin n), @Eq.{1} Real (A i j) (A j i)) →
              (RHat_lower_zero :
                  ∀ (i j : Fin n),
                    @LT.lt.{0} Nat instLTNat (@Fin.val n j) (@Fin.val n i) →
                      @Eq.{1} Real (RHat i j)
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                (off_diagonal_entry :
                    (i j : Fin n) →
                      @LT.lt.{0} Nat instLTNat (@Fin.val n i) (@Fin.val n j) →
                        @HighamBench.P05CholeskyOffDiagonalEntry n format A RHat i j) →
                  (diagonal_entry : (j : Fin n) → @HighamBench.P05CholeskyDiagonalEntry n format A RHat j) →
                    HighamBench.P05CholeskyRun n
```

### D012: `HighamBench.P05FiniteRoundToNearestFormat`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `0ddacc640e57cd98fa542c796ebf4288f8e3c1b48d1de954147bdb407876ca70`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D013: `HighamBench.p05CholeskyPrefixAbsDot`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1cffcc676f8053a7a0f9849a0f2a3636356f00d89aea8b5dc90db721c38817e7`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (R : Fin n → Fin n → Real) → (i j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R i j =>
  Finset.univ.sum fun k =>
    instHMul.hMul (abs (R (HighamBench.p05PrefixIndex i k) i)) (abs (R (HighamBench.p05PrefixIndex i k) j))
```

### D014: `HighamBench.p05CholeskyPrefixDot`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `1057aebd271fd2c8c9ccd0cf3f8db33455dbe774909b5db35813905c5ff4933f`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (R : Fin n → Fin n → Real) → (i j : Fin n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} R i j =>
  Finset.univ.sum fun k => instHMul.hMul (R (HighamBench.p05PrefixIndex i k) i) (R (HighamBench.p05PrefixIndex i k) j)
```

### D015: `HighamBench.P05CholeskyDiagonalEntry`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `06383d2b1bc9a95b0434e8a37fc1ef79218b8a7312d0c0af6998090db989b88f`

Type:

```lean
{n : Nat} → HighamBench.P05FiniteRoundToNearestFormat → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Type
```

Fully explicit type:

```lean
{n : Nat} → (fmt : HighamBench.P05FiniteRoundToNearestFormat) → (A R : Fin n → Fin n → Real) → (j : Fin n) → Type
```

### D016: `HighamBench.P05CholeskyOffDiagonalEntry`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `0e6e9336a7d716aaaabffb6fb4851cf40182274054c03a455380beff5f803c4b`

Type:

```lean
{n : Nat} →
  HighamBench.P05FiniteRoundToNearestFormat → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Type
```

Fully explicit type:

```lean
{n : Nat} → (fmt : HighamBench.P05FiniteRoundToNearestFormat) → (A R : Fin n → Fin n → Real) → (i j : Fin n) → Type
```

### D017: `HighamBench.P05FiniteRoundToNearestFormat.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `12567c74ebb12a1d6821773c68b68a5d2df28fa0be58bacf4154a30b87c2b81e`

Type:

```lean
(radix precision : Nat) →
  (minExponent maxExponent : Int) →
    instLENat.le 2 radix →
      instLTNat.lt 0 precision →
        Int.instLTInt.lt minExponent maxExponent →
          (representable : Real → Prop) →
            (setOf fun x => representable x).Finite →
              (safeRange : Real → Prop) →
                (round : Real → Real) →
                  (unitRoundoff : Real) →
                    Real.instLE.le 0 unitRoundoff →
                      Eq
                          (instHMul.hMul unitRoundoff
                            (instHMul.hMul 2 (instHPow.hPow radix.cast (instHSub.hSub precision 1))))
                          1 →
                        representable 0 →
                          representable 1 →
                            (∀ (x : Real), safeRange x → representable (round x)) →
                              (∀ (x : Real),
                                  safeRange x →
                                    ∀ (z : Real),
                                      representable z →
                                        Real.instLE.le (abs (instHSub.hSub x (round x))) (abs (instHSub.hSub x z))) →
                                (∀ (x : Real), representable x → Eq (round x) x) →
                                  HighamBench.P05FiniteRoundToNearestFormat
```

Fully explicit type:

```lean
(radix precision : Nat) →
  (minExponent maxExponent : Int) →
    (radix_ge_two : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) radix) →
      (precision_pos :
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) precision) →
        (exponent_range_nonempty : @LT.lt.{0} Int Int.instLTInt minExponent maxExponent) →
          (representable : Real → Prop) →
            (representable_finite : @Set.Finite.{0} Real (@setOf.{0} Real fun (x : Real) => representable x)) →
              (safeRange : Real → Prop) →
                (round : Real → Real) →
                  (unitRoundoff : Real) →
                    (unitRoundoff_nonneg :
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) unitRoundoff) →
                      (unitRoundoff_scale :
                          @Eq.{1} Real
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) unitRoundoff
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast radix)
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) precision
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                        (zero_representable :
                            representable (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                          (one_representable :
                              representable (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                            (round_representable : ∀ (x : Real), safeRange x → representable (round x)) →
                              (round_nearest :
                                  ∀ (x : Real),
                                    safeRange x →
                                      ∀ (z : Real),
                                        representable z →
                                          @LE.le.{0} Real Real.instLE
                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x
                                                (round x)))
                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) x
                                                z))) →
                                (round_exact : ∀ (x : Real), representable x → @Eq.{1} Real (round x) x) →
                                  HighamBench.P05FiniteRoundToNearestFormat
```

### D018: `HighamBench.P05FiniteRoundToNearestFormat.representable`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `939843e6234b6b60e9493201a37a6f0770ba8ba2ffd11eb2e38ddcaa236b4ed2`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P05FiniteRoundToNearestFormat) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D019: `HighamBench.p05PrefixIndex`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `702d4429ada9455cd5959efae9f932331aeac5d37604b4119d20204d6d9270c3`

Type:

```lean
{n : Nat} → (k : Fin n) → Fin k.val → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (k : Fin n) → (s : Fin (@Fin.val n k)) → Fin n
```

Definition body (one-level semantic boundary):

```lean
fun {n} k s => ⟨s.val, ⋯⟩
```

### D020: `HighamBench.P05CholeskyDiagonalEntry.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `0c733ccd20eecba3e5907f71ab5ac2dc27055072c009485cb963c0ad3559184a`

Type:

```lean
{n : Nat} →
  {fmt : HighamBench.P05FiniteRoundToNearestFormat} →
    {A R : Fin n → Fin n → Real} →
      {j : Fin n} →
        (execution : HighamBench.P05Lemma43Run j.val) →
          Eq execution.format fmt →
            (∀ (k : Fin j.val), Eq (execution.a k) (R (HighamBench.p05PrefixIndex j k) j)) →
              (∀ (k : Fin j.val), Eq (execution.b k) (R (HighamBench.p05PrefixIndex j k) j)) →
                Eq execution.c (A j j) → Eq execution.yHat (R j j) → HighamBench.P05CholeskyDiagonalEntry fmt A R j
```

Fully explicit type:

```lean
{n : Nat} →
  {fmt : HighamBench.P05FiniteRoundToNearestFormat} →
    {A R : Fin n → Fin n → Real} →
      {j : Fin n} →
        (execution : HighamBench.P05Lemma43Run (@Fin.val n j)) →
          (format_eq :
              @Eq.{1} HighamBench.P05FiniteRoundToNearestFormat
                (@HighamBench.P05Lemma43Run.format (@Fin.val n j) execution) fmt) →
            (left_input_eq :
                ∀ (k : Fin (@Fin.val n j)),
                  @Eq.{1} Real (@HighamBench.P05Lemma43Run.a (@Fin.val n j) execution k)
                    (R (@HighamBench.p05PrefixIndex n j k) j)) →
              (right_input_eq :
                  ∀ (k : Fin (@Fin.val n j)),
                    @Eq.{1} Real (@HighamBench.P05Lemma43Run.b (@Fin.val n j) execution k)
                      (R (@HighamBench.p05PrefixIndex n j k) j)) →
                (protected_input_eq : @Eq.{1} Real (@HighamBench.P05Lemma43Run.c (@Fin.val n j) execution) (A j j)) →
                  (computed_output_eq :
                      @Eq.{1} Real (@HighamBench.P05Lemma43Run.yHat (@Fin.val n j) execution) (R j j)) →
                    @HighamBench.P05CholeskyDiagonalEntry n fmt A R j
```

### D021: `HighamBench.P05CholeskyOffDiagonalEntry.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `5d2f5dcf2ac8406732f77ce10218e9f691b67d820f30b097199a98152557e88d`

Type:

```lean
{n : Nat} →
  {fmt : HighamBench.P05FiniteRoundToNearestFormat} →
    {A R : Fin n → Fin n → Real} →
      {i j : Fin n} →
        (execution : HighamBench.P05Lemma41Run i.val) →
          Eq execution.format fmt →
            (∀ (k : Fin i.val), Eq (execution.a k) (R (HighamBench.p05PrefixIndex i k) i)) →
              (∀ (k : Fin i.val), Eq (execution.b k) (R (HighamBench.p05PrefixIndex i k) j)) →
                Eq execution.bK (R i i) →
                  Eq execution.c (A i j) →
                    Eq execution.yHat (R i j) → HighamBench.P05CholeskyOffDiagonalEntry fmt A R i j
```

Fully explicit type:

```lean
{n : Nat} →
  {fmt : HighamBench.P05FiniteRoundToNearestFormat} →
    {A R : Fin n → Fin n → Real} →
      {i j : Fin n} →
        (execution : HighamBench.P05Lemma41Run (@Fin.val n i)) →
          (format_eq :
              @Eq.{1} HighamBench.P05FiniteRoundToNearestFormat
                (@HighamBench.P05Lemma41Run.format (@Fin.val n i) execution) fmt) →
            (left_input_eq :
                ∀ (k : Fin (@Fin.val n i)),
                  @Eq.{1} Real (@HighamBench.P05Lemma41Run.a (@Fin.val n i) execution k)
                    (R (@HighamBench.p05PrefixIndex n i k) i)) →
              (right_input_eq :
                  ∀ (k : Fin (@Fin.val n i)),
                    @Eq.{1} Real (@HighamBench.P05Lemma41Run.b (@Fin.val n i) execution k)
                      (R (@HighamBench.p05PrefixIndex n i k) j)) →
                (denominator_eq : @Eq.{1} Real (@HighamBench.P05Lemma41Run.bK (@Fin.val n i) execution) (R i i)) →
                  (protected_input_eq : @Eq.{1} Real (@HighamBench.P05Lemma41Run.c (@Fin.val n i) execution) (A i j)) →
                    (computed_output_eq :
                        @Eq.{1} Real (@HighamBench.P05Lemma41Run.yHat (@Fin.val n i) execution) (R i j)) →
                      @HighamBench.P05CholeskyOffDiagonalEntry n fmt A R i j
```

### D022: `HighamBench.p05PrefixIndex._proof_1`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `5e79f8abda33d6147717bad7b59dcf91acde006099614092f0e02069833b9bac`

Type:

```lean
∀ {n : Nat} (k : Fin n) (s : Fin k.val), Nat.instPreorder.lt s.val n
```

Fully explicit type:

```lean
∀ {n : Nat} (k : Fin n) (s : Fin (@Fin.val n k)),
  @LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder) (@Fin.val (@Fin.val n k) s) n
```

### D023: `HighamBench.P05Lemma41Run`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `54f7fb21338d460d95ba24f4f68ec1e88485ff544bfc11cf2639399316ad8dad`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(m : Nat) → Type
```

### D024: `HighamBench.P05Lemma41Run.a`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c74f6cc7255c2553bd8a9833b413e7541ce56f438556ea843f8fc99f4156b157`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.2
```

### D025: `HighamBench.P05Lemma41Run.b`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bad0fe7139c08bbb1859577b06ffb3ed0e035d3317d600ae0b0da9051afed006`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.3
```

### D026: `HighamBench.P05Lemma41Run.bK`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `91a236cf4b3aba3f088617d30f2b25bdb2774e5b236857b4989ee1b529b3db9e`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.4
```

### D027: `HighamBench.P05Lemma41Run.c`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `efe594e7c21046e128f080bccd7ed684eaf4183c2a331fb724ec19789e7e476a`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.5
```

### D028: `HighamBench.P05Lemma41Run.format`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `aadc2a3d9c85a3ab5b73d3632b6c83d3467e27ed03f5d86fced67a9d0489ddc8`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → HighamBench.P05FiniteRoundToNearestFormat
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → HighamBench.P05FiniteRoundToNearestFormat
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.1
```

### D029: `HighamBench.P05Lemma41Run.yHat`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `24b9b4796c449d802022b0dc73b1270acab8eb937804ebf1c6169ecba412af34`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma41Run m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma41Run m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.17
```

### D030: `HighamBench.P05Lemma43Run`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `a3b608ba09a1c8e4568eaf378c8027b7864dd159a1fd63f8734653c0a0b085a2`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(m : Nat) → Type
```

### D031: `HighamBench.P05Lemma43Run.a`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c0b83347e74009ec5343810ec89dbfdc8df6d03212b2ea61c14191ad64841a4f`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma43Run m → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma43Run m) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.2
```

### D032: `HighamBench.P05Lemma43Run.b`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `106215a1f90fb01f0bd73aef8aca01594597612374ba244c1345feb132534fe2`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma43Run m → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma43Run m) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.3
```

### D033: `HighamBench.P05Lemma43Run.c`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7e79ebed3a2b36fb300dc6b4282c3fdd49210fda90137a7ec769a1922d4fa4ec`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma43Run m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma43Run m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.4
```

### D034: `HighamBench.P05Lemma43Run.format`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `34364571f185b8369e0ab4e3be98cd6d3d0f5d19c2db0dab84d394e42b8bb11f`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma43Run m → HighamBench.P05FiniteRoundToNearestFormat
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma43Run m) → HighamBench.P05FiniteRoundToNearestFormat
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.1
```

### D035: `HighamBench.P05Lemma43Run.yHat`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bd863edf54a1701a00190bae20218cbc6dc6f4c31b992997ead72451557c723d`

Type:

```lean
{m : Nat} → HighamBench.P05Lemma43Run m → Real
```

Fully explicit type:

```lean
{m : Nat} → (self : HighamBench.P05Lemma43Run m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m self => self.16
```

### D036: `HighamBench.P05Lemma41Run.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `c846b40599e7d4a3d66b55c917495caee8618b1e9b0f894f80f5936e203a1201`

Type:

```lean
{m : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    (a b : Fin m → Real) →
      (bK c : Real) →
        (∀ (i : Fin m), format.representable (a i)) →
          (∀ (i : Fin m), format.representable (b i)) →
            format.representable bK →
              format.representable c →
                Ne bK 0 →
                  (∀ (i : Fin m), format.safeRange (instHMul.hMul (a i) (b i))) →
                    (tree : HighamBench.P05SumTree (instHAdd.hAdd m 1)) →
                      (order : Equiv.Perm (Fin (instHAdd.hAdd m 1))) →
                        (HighamBench.p05SumTreeSafe format tree fun i =>
                            HighamBench.p05Lemma41Summands format a b c (EquivLike.toFunLike.coe order i)) →
                          (numerator : Real) →
                            Eq numerator
                                (HighamBench.p05SumTreeEval format tree fun i =>
                                  HighamBench.p05Lemma41Summands format a b c (EquivLike.toFunLike.coe order i)) →
                              (yHat : Real) →
                                (Eq bK 1 → Eq yHat numerator) →
                                  (Ne bK 1 → format.safeRange (instHDiv.hDiv numerator bK)) →
                                    (Ne bK 1 → Eq yHat (format.round (instHDiv.hDiv numerator bK))) →
                                      Real.instLE.le
                                          (abs
                                            (instHSub.hSub
                                              (instHSub.hSub c (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                              (instHMul.hMul bK yHat)))
                                          (instHMul.hMul (instHMul.hMul (instHAdd.hAdd m 1).cast format.unitRoundoff)
                                            (instHAdd.hAdd (abs (instHMul.hMul bK yHat))
                                              (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i))))) →
                                        (Eq bK 1 →
                                            Real.instLE.le
                                              (abs
                                                (instHSub.hSub
                                                  (instHSub.hSub c (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                                  yHat))
                                              (instHMul.hMul (instHMul.hMul m.cast format.unitRoundoff)
                                                (instHAdd.hAdd (abs yHat)
                                                  (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i)))))) →
                                          HighamBench.P05Lemma41Run m
```

Fully explicit type:

```lean
{m : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    (a b : Fin m → Real) →
      (bK c : Real) →
        (a_representable : ∀ (i : Fin m), HighamBench.P05FiniteRoundToNearestFormat.representable format (a i)) →
          (b_representable : ∀ (i : Fin m), HighamBench.P05FiniteRoundToNearestFormat.representable format (b i)) →
            (bK_representable : HighamBench.P05FiniteRoundToNearestFormat.representable format bK) →
              (c_representable : HighamBench.P05FiniteRoundToNearestFormat.representable format c) →
                (bK_nonzero :
                    @Ne.{1} Real bK (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                  (product_safe :
                      ∀ (i : Fin m),
                        HighamBench.P05FiniteRoundToNearestFormat.safeRange format
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a i) (b i))) →
                    (tree :
                        HighamBench.P05SumTree
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      (order :
                          Equiv.Perm.{1}
                            (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                        (tree_safe :
                            @HighamBench.p05SumTreeSafe format
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              tree
                              fun
                                (i :
                                  Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                              @HighamBench.p05Lemma41Summands m format a b c
                                (@DFunLike.coe.{1, 1, 1}
                                  (Equiv.Perm.{1}
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (fun
                                      (x :
                                        Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                    Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (@EquivLike.toFunLike.{1, 1, 1}
                                    (Equiv.Perm.{1}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Equiv.instEquivLike.{1, 1}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                  order i)) →
                          (numerator : Real) →
                            (numerator_eq :
                                @Eq.{1} Real numerator
                                  (@HighamBench.p05SumTreeEval format
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    tree
                                    fun
                                      (i :
                                        Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                    @HighamBench.p05Lemma41Summands m format a b c
                                      (@DFunLike.coe.{1, 1, 1}
                                        (Equiv.Perm.{1}
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (fun
                                            (x :
                                              Fin
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                          Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@EquivLike.toFunLike.{1, 1, 1}
                                          (Equiv.Perm.{1}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                          (@Equiv.instEquivLike.{1, 1}
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                        order i))) →
                              (yHat : Real) →
                                (no_division_when_unit :
                                    @Eq.{1} Real bK
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                      @Eq.{1} Real yHat numerator) →
                                  (division_safe :
                                      @Ne.{1} Real bK
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                        HighamBench.P05FiniteRoundToNearestFormat.safeRange format
                                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                            numerator bK)) →
                                    (rounded_division :
                                        @Ne.{1} Real bK
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                          @Eq.{1} Real yHat
                                            (HighamBench.P05FiniteRoundToNearestFormat.round format
                                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                (@instHDiv.{0} Real
                                                  (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                numerator bK))) →
                                      (general_residual_bound :
                                          @LE.le.{0} Real Real.instLE
                                            (@abs.{0} Real Real.lattice Real.instAddGroup
                                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) c
                                                  (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                    (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                    @HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul) (a i) (b i)))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  bK yHat)))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@Nat.cast.{0} Real Real.instNatCast
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff format))
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    bK yHat))
                                                (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                  (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                  @abs.{0} Real Real.lattice Real.instAddGroup
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul) (a i) (b i)))))) →
                                        (unit_residual_bound :
                                            @Eq.{1} Real bK
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne)) →
                                              @LE.le.{0} Real Real.instLE
                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                                    (@HSub.hSub.{0, 0, 0} Real Real Real
                                                      (@instHSub.{0} Real Real.instSub) c
                                                      (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                        (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                        @HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) (a i) (b i)))
                                                    yHat))
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@Nat.cast.{0} Real Real.instNatCast m)
                                                    (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff format))
                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                    (@abs.{0} Real Real.lattice Real.instAddGroup yHat)
                                                    (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                      (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                      @abs.{0} Real Real.lattice Real.instAddGroup
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) (a i) (b i)))))) →
                                          HighamBench.P05Lemma41Run m
```

### D037: `HighamBench.P05Lemma43Run.mk`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `2c9f907b9c0860ab964e21c3a2441a16c6a4b1a5e517b86972b82d7d9dc74cc1`

Type:

```lean
{m : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    (a b : Fin m → Real) →
      (c : Real) →
        (∀ (i : Fin m), format.representable (a i)) →
          (∀ (i : Fin m), format.representable (b i)) →
            format.representable c →
              (∀ (i : Fin m), format.safeRange (instHMul.hMul (a i) (b i))) →
                (tree : HighamBench.P05SumTree (instHAdd.hAdd m 1)) →
                  (order : Equiv.Perm (Fin (instHAdd.hAdd m 1))) →
                    (HighamBench.p05SumTreeSafe format tree fun i =>
                        HighamBench.p05Lemma41Summands format a b c (EquivLike.toFunLike.coe order i)) →
                      (numerator : Real) →
                        Eq numerator
                            (HighamBench.p05SumTreeEval format tree fun i =>
                              HighamBench.p05Lemma41Summands format a b c (EquivLike.toFunLike.coe order i)) →
                          Real.instLE.le 0 numerator →
                            format.safeRange numerator.sqrt →
                              (yHat : Real) →
                                Eq yHat (format.round numerator.sqrt) →
                                  Real.instLE.le 0 yHat →
                                    Real.instLE.le
                                        (abs
                                          (instHSub.hSub
                                            (instHSub.hSub c (Finset.univ.sum fun i => instHMul.hMul (a i) (b i)))
                                            (instHPow.hPow yHat 2)))
                                        (instHMul.hMul (instHMul.hMul (instHAdd.hAdd m 2).cast format.unitRoundoff)
                                          (instHAdd.hAdd (abs (instHPow.hPow yHat 2))
                                            (Finset.univ.sum fun i => abs (instHMul.hMul (a i) (b i))))) →
                                      HighamBench.P05Lemma43Run m
```

Fully explicit type:

```lean
{m : Nat} →
  (format : HighamBench.P05FiniteRoundToNearestFormat) →
    (a b : Fin m → Real) →
      (c : Real) →
        (a_representable : ∀ (i : Fin m), HighamBench.P05FiniteRoundToNearestFormat.representable format (a i)) →
          (b_representable : ∀ (i : Fin m), HighamBench.P05FiniteRoundToNearestFormat.representable format (b i)) →
            (c_representable : HighamBench.P05FiniteRoundToNearestFormat.representable format c) →
              (product_safe :
                  ∀ (i : Fin m),
                    HighamBench.P05FiniteRoundToNearestFormat.safeRange format
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (a i) (b i))) →
                (tree :
                    HighamBench.P05SumTree
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (order :
                      Equiv.Perm.{1}
                        (Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                    (tree_safe :
                        @HighamBench.p05SumTreeSafe format
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          tree
                          fun
                            (i :
                              Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                          @HighamBench.p05Lemma41Summands m format a b c
                            (@DFunLike.coe.{1, 1, 1}
                              (Equiv.Perm.{1}
                                (Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (fun
                                  (x :
                                    Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (@EquivLike.toFunLike.{1, 1, 1}
                                (Equiv.Perm.{1}
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                (Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (@Equiv.instEquivLike.{1, 1}
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              order i)) →
                      (numerator : Real) →
                        (numerator_eq :
                            @Eq.{1} Real numerator
                              (@HighamBench.p05SumTreeEval format
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                tree
                                fun
                                  (i :
                                    Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                @HighamBench.p05Lemma41Summands m format a b c
                                  (@DFunLike.coe.{1, 1, 1}
                                    (Equiv.Perm.{1}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (fun
                                        (x :
                                          Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
                                      Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@EquivLike.toFunLike.{1, 1, 1}
                                      (Equiv.Perm.{1}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                    order i))) →
                          (numerator_nonneg :
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) numerator) →
                            (sqrt_safe :
                                HighamBench.P05FiniteRoundToNearestFormat.safeRange format (Real.sqrt numerator)) →
                              (yHat : Real) →
                                (rounded_sqrt :
                                    @Eq.{1} Real yHat
                                      (HighamBench.P05FiniteRoundToNearestFormat.round format (Real.sqrt numerator))) →
                                  (yHat_nonneg :
                                      @LE.le.{0} Real Real.instLE
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                        yHat) →
                                    (sqrt_residual_bound :
                                        @LE.le.{0} Real Real.instLE
                                          (@abs.{0} Real Real.lattice Real.instAddGroup
                                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) c
                                                (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                  (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                  @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (a i) (b i)))
                                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                yHat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@Nat.cast.{0} Real Real.instNatCast
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              (HighamBench.P05FiniteRoundToNearestFormat.unitRoundoff format))
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                  (@instHPow.{0, 0} Real Nat
                                                    (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                  yHat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid
                                                (@Finset.univ.{0} (Fin m) (Fin.fintype m)) fun (i : Fin m) =>
                                                @abs.{0} Real Real.lattice Real.instAddGroup
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (a i) (b i)))))) →
                                      HighamBench.P05Lemma43Run m
```

### D038: `HighamBench.P05FiniteRoundToNearestFormat.round`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `0bebeeb156b3b1d6c4fb9f9ec0c12486071422fb52bff0d1206d805e87292cbc`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P05FiniteRoundToNearestFormat) → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.11
```

### D039: `HighamBench.P05FiniteRoundToNearestFormat.safeRange`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `6b66b03c590cc2c1654bd9631fb5645291a21681e905b136a1f85d1fd928c436`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → Real → Prop
```

Fully explicit type:

```lean
(self : HighamBench.P05FiniteRoundToNearestFormat) → Real → Prop
```

Definition body (one-level semantic boundary):

```lean
fun self => self.10
```

### D040: `HighamBench.P05SumTree`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `inductive`
- Distance from target type: `7`
- Semantic SHA-256: `443a0aa6f83664582344d89f72b609bc7af3d2025eacff100aebdbcacb0938fc`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
Nat → Type
```

### D041: `HighamBench.p05Lemma41Summands`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `53288ef5dcd6dce907f195ffd0fdcbfaebf7b436ac8098403000f49182a3ede0`

Type:

```lean
{m : Nat} →
  HighamBench.P05FiniteRoundToNearestFormat → (Fin m → Real) → (Fin m → Real) → Real → Fin (instHAdd.hAdd m 1) → Real
```

Fully explicit type:

```lean
{m : Nat} →
  (fmt : HighamBench.P05FiniteRoundToNearestFormat) →
    (a b : Fin m → Real) →
      (c : Real) →
        Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b c i => Fin.cases c (fun i => Real.instNeg.neg (HighamBench.p05RoundedProducts fmt a b i)) i
```

### D042: `HighamBench.p05SumTreeEval`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `5276000dc42400351a4955f3911dcae4de8b74de2fb84b50d07230a884af2020`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → {n : Nat} → HighamBench.P05SumTree n → (Fin n → Real) → Real
```

Fully explicit type:

```lean
(fmt : HighamBench.P05FiniteRoundToNearestFormat) →
  {n : Nat} → (tree : HighamBench.P05SumTree n) → (v : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  HighamBench.P05SumTree.brecOn (motive := fun {n} tree => (Fin n → Real) → Real) tree
    (fun {n} tree f v =>
      HighamBench.p05SumTreeEval.match_1
        (fun n tree v => HighamBench.P05SumTree.below (motive := fun {n} tree => (Fin n → Real) → Real) tree → Real) n
        tree v (fun v x => v ⟨0, HighamBench.p05SumTreeEval._proof_1⟩)
        (fun m n left right v x =>
          fmt.round (instHAdd.hAdd (x.1.1 fun i => v (Fin.castAdd n i)) (x.2.1 fun i => v (Fin.natAdd m i))))
        f)
    v
```

### D043: `HighamBench.p05SumTreeSafe`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `28c67f1f1f332ec7ed8f24f988fff25480a126aa5735959a513d27837bc19587`

Type:

```lean
HighamBench.P05FiniteRoundToNearestFormat → {n : Nat} → HighamBench.P05SumTree n → (Fin n → Real) → Prop
```

Fully explicit type:

```lean
(fmt : HighamBench.P05FiniteRoundToNearestFormat) →
  {n : Nat} → (tree : HighamBench.P05SumTree n) → (v : Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun fmt {n} tree v =>
  HighamBench.P05SumTree.brecOn (motive := fun {n} tree => (Fin n → Real) → Prop) tree
    (fun {n} tree f v =>
      HighamBench.p05SumTreeEval.match_1
        (fun n tree v => HighamBench.P05SumTree.below (motive := fun {n} tree => (Fin n → Real) → Prop) tree → Prop) n
        tree v (fun v x => fmt.representable (v ⟨0, HighamBench.p05SumTreeEval._proof_1⟩))
        (fun m n left right v x =>
          And (x.1.1 fun i => v (Fin.castAdd n i))
            (And (x.2.1 fun i => v (Fin.natAdd m i))
              (fmt.safeRange
                (instHAdd.hAdd (HighamBench.p05SumTreeEval fmt left fun i => v (Fin.castAdd n i))
                  (HighamBench.p05SumTreeEval fmt right fun i => v (Fin.natAdd m i))))))
        f)
    v
```

### D044: `HighamBench.P05SumTree.below`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `04678a12719fff926622b3e9fbf38f572093e387c69fa03eb32cb222cd68fe1a`

Type:

```lean
{motive : (a : Nat) → HighamBench.P05SumTree a → Sort u} → {a : Nat} → HighamBench.P05SumTree a → Sort (max 1 u)
```

Fully explicit type:

```lean
{motive : (a : Nat) → (t : HighamBench.P05SumTree a) → Sort u} →
  {a : Nat} → (t : HighamBench.P05SumTree a) → Sort (max 1 u)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t =>
  HighamBench.P05SumTree.rec PUnit
    (fun {m n} a a_1 a_ih a_ih_1 => PProd (PProd (motive m a) a_ih) (PProd (motive n a_1) a_ih_1)) t
```

### D045: `HighamBench.P05SumTree.brecOn`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `cb3c6322835a978db412df67d07972af7f5ebc95b2fe7fffd3f78ab7c1c10544`

Type:

```lean
{motive : (a : Nat) → HighamBench.P05SumTree a → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      ((a : Nat) → (t : HighamBench.P05SumTree a) → HighamBench.P05SumTree.below t → motive a t) → motive a t
```

Fully explicit type:

```lean
{motive : (a : Nat) → (t : HighamBench.P05SumTree a) → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      (F_1 :
          (a : Nat) →
            (t : HighamBench.P05SumTree a) → (f : @HighamBench.P05SumTree.below.{u} motive a t) → motive a t) →
        motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 => (HighamBench.P05SumTree.brecOn.go t F_1).1
```

### D046: `HighamBench.P05SumTree.leaf`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `d400482110f6735443dd560bbbc8525a6db52e539e45f92488e808fd742cb999`

Type:

```lean
HighamBench.P05SumTree 1
```

Fully explicit type:

```lean
HighamBench.P05SumTree (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
```

### D047: `HighamBench.P05SumTree.node`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `constructor`
- Distance from target type: `8`
- Semantic SHA-256: `47eb0dcdab89e52469860668ea9ff917c63ab85960c92a40c58d7885ba4b7f44`

Type:

```lean
{m n : Nat} → HighamBench.P05SumTree m → HighamBench.P05SumTree n → HighamBench.P05SumTree (instHAdd.hAdd m n)
```

Fully explicit type:

```lean
{m n : Nat} →
  HighamBench.P05SumTree m →
    HighamBench.P05SumTree n →
      HighamBench.P05SumTree (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)
```

### D048: `HighamBench.p05RoundedProducts`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `9cc6e82bd9680cd814e1f49e1260fe201a0535af0efdf7c523fa734c4b1cf26e`

Type:

```lean
{m : Nat} → HighamBench.P05FiniteRoundToNearestFormat → (Fin m → Real) → (Fin m → Real) → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} → (fmt : HighamBench.P05FiniteRoundToNearestFormat) → (a b : Fin m → Real) → Fin m → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} fmt a b i => fmt.round (instHMul.hMul (a i) (b i))
```

### D049: `HighamBench.p05SumTreeEval._proof_1`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `theorem`
- Distance from target type: `8`
- Semantic SHA-256: `3837ff05fe96904abf1d46536ea66370e1afc147c8f02d6219701e1854673c5f`

Type:

```lean
Nat.instPartialOrder.lt 0 1
```

Fully explicit type:

```lean
@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat (@PartialOrder.toPreorder.{0} Nat Nat.instPartialOrder))
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
```

### D050: `HighamBench.p05SumTreeEval.match_1`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `628dea76c4d1a3a85ca7248eb8dbbe9298030d0d3d089ceb2f318990b1196f40`

Type:

```lean
(motive : (n : Nat) → HighamBench.P05SumTree n → (Fin n → Real) → Sort u_1) →
  (n : Nat) →
    (tree : HighamBench.P05SumTree n) →
      (v : Fin n → Real) →
        ((v : Fin 1 → Real) → motive 1 HighamBench.P05SumTree.leaf v) →
          ((m n : Nat) →
              (left : HighamBench.P05SumTree m) →
                (right : HighamBench.P05SumTree n) →
                  (v : Fin (instHAdd.hAdd m n) → Real) → motive (instHAdd.hAdd m n) (left.node right) v) →
            motive n tree v
```

Fully explicit type:

```lean
(motive : (n : Nat) → HighamBench.P05SumTree n → (v : Fin n → Real) → Sort u_1) →
  (n : Nat) →
    (tree : HighamBench.P05SumTree n) →
      (v : Fin n → Real) →
        (h_1 :
            (v : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Real) →
              motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HighamBench.P05SumTree.leaf v) →
          (h_2 :
              (m n : Nat) →
                (left : HighamBench.P05SumTree m) →
                  (right : HighamBench.P05SumTree n) →
                    (v : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n) → Real) →
                      motive (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)
                        (@HighamBench.P05SumTree.node m n left right) v) →
            motive n tree v
```

Definition body (one-level semantic boundary):

```lean
fun motive n tree v h_1 h_2 =>
  (fun tree_1 =>
      HighamBench.P05SumTree.casesOn (motive := fun a x => Eq n a → HEq tree x → motive n tree v) tree_1
        (fun h =>
          Eq.ndrec (motive := fun n =>
            (tree : HighamBench.P05SumTree n) →
              (v : Fin n → Real) → HEq tree HighamBench.P05SumTree.leaf → motive n tree v)
            (fun tree v h => Eq.ndrec (h_1 v) ⋯) ⋯ tree v)
        fun {m n_1} a a_1 h =>
        Eq.ndrec (motive := fun n =>
          (tree : HighamBench.P05SumTree n) → (v : Fin n → Real) → HEq tree (a.node a_1) → motive n tree v)
          (fun tree v h => Eq.ndrec (h_2 m n_1 a a_1 v) ⋯) ⋯ tree v)
    tree ⋯ ⋯
```

### D051: `HighamBench.P05SumTree.brecOn.go`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `a1f5b5d0ff724fb25f8c6eb41f3392a734a4bd8a54fa24702cb5c1c49c98e9b7`

Type:

```lean
{motive : (a : Nat) → HighamBench.P05SumTree a → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      ((a : Nat) → (t : HighamBench.P05SumTree a) → HighamBench.P05SumTree.below t → motive a t) →
        PProd (motive a t) (HighamBench.P05SumTree.below t)
```

Fully explicit type:

```lean
{motive : (a : Nat) → (t : HighamBench.P05SumTree a) → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      (F_1 :
          (a : Nat) →
            (t : HighamBench.P05SumTree a) → (f : @HighamBench.P05SumTree.below.{u} motive a t) → motive a t) →
        PProd.{u, max 1 u} (motive a t) (@HighamBench.P05SumTree.below.{u} motive a t)
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t F_1 =>
  HighamBench.P05SumTree.rec ⟨F_1 1 HighamBench.P05SumTree.leaf PUnit.unit, PUnit.unit⟩
    (fun {m n} a a_1 a_ih a_ih_1 => ⟨F_1 (instHAdd.hAdd m n) (a.node a_1) ⟨a_ih, a_ih_1⟩, a_ih, a_ih_1⟩) t
```

### D052: `HighamBench.P05SumTree.casesOn`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `6a2f271359e9f74faaece28f70b9cc38b461b3d2ac2b2cacdbb565586e6814f8`

Type:

```lean
{motive : (a : Nat) → HighamBench.P05SumTree a → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      motive 1 HighamBench.P05SumTree.leaf →
        ({m n : Nat} →
            (a : HighamBench.P05SumTree m) →
              (a_1 : HighamBench.P05SumTree n) → motive (instHAdd.hAdd m n) (a.node a_1)) →
          motive a t
```

Fully explicit type:

```lean
{motive : (a : Nat) → (t : HighamBench.P05SumTree a) → Sort u} →
  {a : Nat} →
    (t : HighamBench.P05SumTree a) →
      (leaf : motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HighamBench.P05SumTree.leaf) →
        (node :
            {m n : Nat} →
              (a : HighamBench.P05SumTree m) →
                (a_1 : HighamBench.P05SumTree n) →
                  motive (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)
                    (@HighamBench.P05SumTree.node m n a a_1)) →
          motive a t
```

Definition body (one-level semantic boundary):

```lean
fun {motive} {a} t leaf node => HighamBench.P05SumTree.rec leaf (fun {m n} a a_1 a_ih a_ih_1 => node a a_1) t
```

### D053: `HighamBench.P05SumTree.rec`

- Role: `local`
- Owner module: `HighamBench.P05Definitions`
- Declaration kind: `recursor`
- Distance from target type: `9`
- Semantic SHA-256: `9b30df98c9e7570f0a4522ebeddf3fffb65f3cfaa16bd8c18752e6df00414a03`

Type:

```lean
{motive : (a : Nat) → HighamBench.P05SumTree a → Sort u} →
  motive 1 HighamBench.P05SumTree.leaf →
    ({m n : Nat} →
        (a : HighamBench.P05SumTree m) →
          (a_1 : HighamBench.P05SumTree n) → motive m a → motive n a_1 → motive (instHAdd.hAdd m n) (a.node a_1)) →
      {a : Nat} → (t : HighamBench.P05SumTree a) → motive a t
```

Fully explicit type:

```lean
{motive : (a : Nat) → (t : HighamBench.P05SumTree a) → Sort u} →
  (leaf : motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) HighamBench.P05SumTree.leaf) →
    (node :
        {m n : Nat} →
          (a : HighamBench.P05SumTree m) →
            (a_1 : HighamBench.P05SumTree n) →
              motive m a →
                motive n a_1 →
                  motive (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m n)
                    (@HighamBench.P05SumTree.node m n a a_1)) →
      {a : Nat} → (t : HighamBench.P05SumTree a) → motive a t
```

### D054: `And`

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

### D055: `Eq`

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

### D056: `Exists`

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

### D057: `Fin`

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

### D058: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `74cc6296b3a13207507ec372ef420f5e52b6935895dd25bcc6331abde2a4b328`

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

### D059: `HAdd.hAdd`

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

### D060: `HMul.hMul`

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

### D061: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `98025b38d523c0eadea77ba4961a20b2a913b23c079c4bfeba24a7bfaa24a4bc`

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

### D062: `LE.le`

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

### D063: `LT.lt`

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

### D064: `Nat`

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

### D065: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D066: `OfNat.ofNat`

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

### D067: `Pi.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Notation.Pi.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `786aa93e85ac0acc746f4c8ee6aed957d52e0231f66623c2b8e478a794d15ce0`

Type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add (M i)] → Add ((i : ι) → M i)
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : ι → Type u_5} → [(i : ι) → Add.{u_5} (M i)] → Add.{max u_1 u_5} ((i : ι) → M i)
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [(i : ι) → Add (M i)] => { add := fun f g i => instHAdd.hAdd (f i) (g i) }
```

### D068: `Real`

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

### D069: `Real.instAdd`

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

### D070: `Real.instAddGroup`

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

### D071: `Real.instLE`

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

### D072: `Real.instMul`

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

### D073: `Real.instNatCast`

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

### D074: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `926d9e8fcca2819a885d446e168b20c7c8aac2e542d59ed2b48e32c9a4659a36`

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

### D075: `Real.lattice`

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

### D076: `abs`

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

### D077: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D078: `instHAdd`

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

### D079: `instHMul`

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

### D080: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `aa782f2b5af3d068f4c5340de4b32b193fece2c659a45582cc3024a19b550c87`

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

### D081: `instLTNat`

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

### D082: `instOfNatNat`

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

### D083: `Fin.fintype`

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

### D084: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `931ceac4e9efb5833f58970d10ced4621362e020ea1119492a8d379b7e692372`

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

### D085: `Finset.univ`

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

### D086: `Real.instAddCommMonoid`

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

### D087: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D088: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D089: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D090: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D091: `Int`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `257bf50f640447b541733c8fd9c6bcca584fc9dd85c221eb4f37888655c88e08`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D092: `Int.instLTInt`

- Role: `external-frontier`
- Owner module: `Init.Data.Int.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `c6ba6b2af0ba0b1e59e45f9e25272ad271a1e55993be47eb5029dc9e9dbfc5ab`

Type:

```lean
LT Int
```

Fully explicit type:

```lean
LT.{0} Int
```

Definition body (one-level semantic boundary):

```lean
{ lt := Int.lt }
```

### D093: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5b7373fe2de26535c1cdbf1b953ce34faf30f68aac8abd83ade2e78e6ec65b8a`

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

### D094: `Nat.instAtLeastTwoHAddOfNat`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `theorem`
- Distance from target type: `4`
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

### D095: `Nat.instNeZeroSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `4`
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

### D096: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D097: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `37978679365b30167654c1ef9ecb0fa938325c2047191daa7208aee389c0b4b8`

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

### D098: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D099: `Set.Finite`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Finite.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cd1248ce5442277e3732ae7b908af0837d4e3ee0bff49bbaa908aef80f57bfbc`

Type:

```lean
{α : Type u} → Set α → Prop
```

Fully explicit type:

```lean
{α : Type u} → (s : Set.{u} α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} s => Finite s.Elem
```

### D100: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D101: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `002e628e28a06e89ab80e69408fa3be9fc3e200fafd33e0f71d9111a8944875e`

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

### D102: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D103: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `5b0e20a4d2b3e0a67bd35de1b5c84cc60d6dc867658112d84cad483055804868`

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

### D104: `setOf`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Set.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `cee4433aebd78c308ec85f62ccd30489c00ec9cc23a98f4d2139c17f840f4988`

Type:

```lean
{α : Type u} → (α → Prop) → Set α
```

Fully explicit type:

```lean
{α : Type u} → (p : α → Prop) → Set.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} p => p
```

### D105: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5ea89e9915200c8782bc933f9184e28eb38f4c9610b00cf1310cc6e6435642d8`

Type:

```lean
Preorder Nat
```

Fully explicit type:

```lean
Preorder.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D106: `Preorder.toLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `8fcf5a8f5a8899408a8cdc310bc44f6f7b84a21905a114103fbc65083f779a43`

Type:

```lean
{α : Type u_2} → [self : Preorder α] → LT α
```

Fully explicit type:

```lean
{α : Type u_2} → [self : Preorder.{u_2} α] → LT.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Preorder α] => self.2
```

### D107: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `9db5c150b3c86d10b50e19602d0c0af9e5012dfe5f13b0d7b57925729f2478f0`

Type:

```lean
{F : Sort u_1} → {α : outParam (Sort u_2)} → {β : outParam (α → Sort u_3)} → [self : DFunLike F α β] → F → (a : α) → β a
```

Fully explicit type:

```lean
{F : Sort u_1} →
  {α : outParam.{u_2 + 1} (Sort u_2)} →
    {β : outParam.{max u_2 (u_3 + 1)} (α → Sort u_3)} → [self : DFunLike.{u_1, u_2, u_3} F α β] → F → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun F {α} {β} [self : DFunLike F α β] => self.1
```

### D108: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `7`
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

### D109: `Equiv.Perm`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `c8be4339de7efaee2aff8b13efc12794f5acd112d4188f63d38d39f9e4bd687c`

Type:

```lean
Sort u_1 → Sort (max 1 u_1)
```

Fully explicit type:

```lean
(α : Sort u_1) → Sort (max 1 u_1)
```

Definition body (one-level semantic boundary):

```lean
fun α => Equiv α α
```

### D110: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `c53ba65c6bd0e248eb34b05badc813675bd3ab80452ae652c8efe8beb0652559`

Type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike (Equiv α β) α β
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → EquivLike.{max (max 1 v) u, u, v} (Equiv.{u, v} α β) α β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} => { coe := Equiv.toFun, inv := Equiv.invFun, left_inv := ⋯, right_inv := ⋯, coe_injective' := ⋯ }
```

### D111: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `0f60978070e976ff8040a5b974a5b08a27d74758a8f4361a6276a17c12a1d96a`

Type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike E α β] → FunLike E α β
```

Fully explicit type:

```lean
{E : Sort u_1} → {α : Sort u_3} → {β : Sort u_4} → [EquivLike.{u_1, u_3, u_4} E α β] → FunLike.{u_1, u_3, u_4} E α β
```

Definition body (one-level semantic boundary):

```lean
fun {E} {α} {β} [inst : EquivLike E α β] => { coe := inst.coe, coe_injective' := ⋯ }
```

### D112: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
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

### D113: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `635adc1f9e4a981a5c01b21338fdf89e637bd4ef0aa6911bda4dc03acfe9fba6`

Type:

```lean
{α : Sort u} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u} → (a b : α) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} a b => Not (Eq a b)
```

### D114: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D115: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D116: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D117: `Fin.cases`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Lemmas`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `38edd2256cd8f4f33f2c43ce7c36a1e1c7aded652580ec57a0adaf0ec346b64d`

Type:

```lean
{n : Nat} →
  {motive : Fin (instHAdd.hAdd n 1) → Sort u_1} →
    motive 0 → ((i : Fin n) → motive i.succ) → (i : Fin (instHAdd.hAdd n 1)) → motive i
```

Fully explicit type:

```lean
{n : Nat} →
  {motive :
      Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Sort u_1} →
    (zero :
        motive
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))) →
      (succ : (i : Fin n) → motive (@Fin.succ n i)) →
        (i :
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          motive i
```

Definition body (one-level semantic boundary):

```lean
fun {n} {motive} zero succ i => Fin.induction zero (fun i x => succ i) i
```

### D118: `Fin.castAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `bff7b13dfc77fda725a938338f6d0c6fbe5d5b328cd5c9a1c9de44224915838b`

Type:

```lean
{n : Nat} → (m : Nat) → Fin n → Fin (instHAdd.hAdd n m)
```

Fully explicit type:

```lean
{n : Nat} → (m : Nat) → Fin n → Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n m)
```

Definition body (one-level semantic boundary):

```lean
fun {n} m => Fin.castLE ⋯
```

### D119: `Fin.natAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `06007c678fab1dc171aa2b490b41eb467e5f51799a25bb0c10890e6946480989`

Type:

```lean
{m : Nat} → (n : Nat) → Fin m → Fin (instHAdd.hAdd n m)
```

Fully explicit type:

```lean
{m : Nat} → (n : Nat) → (i : Fin m) → Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n m)
```

Definition body (one-level semantic boundary):

```lean
fun {m} n i => ⟨instHAdd.hAdd n i.val, ⋯⟩
```

### D120: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `8`
- Semantic SHA-256: `0c56662a5d917c211c3cb741ca747b4a6710082af615cf071342ef70dee3a2c7`

Type:

```lean
{α : Type u} → [self : Neg α] → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Neg.{u} α] → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Neg α] => self.1
```

### D121: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `000951397468b3d1f8a2a1cca1de3812bc024916ff842cfd5454811130093b41`

Type:

```lean
Neg Real
```

Fully explicit type:

```lean
Neg.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ neg := Real.neg✝ }
```

### D122: `Eq.ndrec`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `9`
- Semantic SHA-256: `f86cb68b5cbbf1ddc06f9f211e3421eced11542c1e459b8ba4c1e06c0f8ca7d2`

Type:

```lean
{α : Sort u2} → {a : α} → {motive : α → Sort u1} → motive a → {b : α} → Eq a b → motive b
```

Fully explicit type:

```lean
{α : Sort u2} → {a : α} → {motive : α → Sort u1} → (m : motive a) → {b : α} → (h : @Eq.{u2} α a b) → motive b
```

Definition body (one-level semantic boundary):

```lean
fun {α} {a} {motive} m {b} h => Eq.rec m h
```

### D123: `Eq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `9`
- Semantic SHA-256: `62d4020b7012db70e44624c7d64dd267524e7e75e4b869680e0c95d2231c85d1`

Type:

```lean
∀ {α : Sort u_1} (a : α), Eq a a
```

Fully explicit type:

```lean
∀ {α : Sort u_1} (a : α), @Eq.{u_1} α a a
```

### D124: `Eq.symm`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `9`
- Semantic SHA-256: `7c9d5428fd9feab69045077277e3f895072f20edba5f2a9479559efbee9f7cf2`

Type:

```lean
∀ {α : Sort u} {a b : α}, Eq a b → Eq b a
```

Fully explicit type:

```lean
∀ {α : Sort u} {a b : α} (h : @Eq.{u} α a b), @Eq.{u} α b a
```

### D125: `HEq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `a71d8d31511fc844f0f70ae865b109282edf2e9593d6acbdee9925cd9e03d1db`

Type:

```lean
{α : Sort u} → α → {β : Sort u} → β → Prop
```

Fully explicit type:

```lean
{α : Sort u} → α → {β : Sort u} → β → Prop
```

### D126: `HEq.refl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `9`
- Semantic SHA-256: `15ec9e197e90776f1db6670d1ce41d43e6ba50700a0f4752439b345b47e5d1c9`

Type:

```lean
∀ {α : Sort u} (a : α), HEq a a
```

Fully explicit type:

```lean
∀ {α : Sort u} (a : α), @HEq.{u} α a α a
```

### D127: `Nat.instPartialOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `2759981f152e80eec9150e4e0e23de292150f9cea0c8c910125cf9e56acf2f67`

Type:

```lean
PartialOrder Nat
```

Fully explicit type:

```lean
PartialOrder.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D128: `PProd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `f220f3fbfda558146d81aa3a9391a551a0b414f82b31ddca68583a9f3b829035`

Type:

```lean
Sort u → Sort v → Sort (max (max 1 u) v)
```

Fully explicit type:

```lean
(α : Sort u) → (β : Sort v) → Sort (max (max 1 u) v)
```

### D129: `PUnit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `9`
- Semantic SHA-256: `766f980214e36af1ff35d2ec98c8393266d25d4a847f71e22766f564898fc02c`

Type:

```lean
Sort u
```

Fully explicit type:

```lean
Sort u
```

### D130: `PartialOrder.toPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Defs.PartialOrder`
- Declaration kind: `abbrev`
- Distance from target type: `9`
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

### D131: `eq_of_heq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `theorem`
- Distance from target type: `9`
- Semantic SHA-256: `17dda0f4fb758715279a058b25c7babf034d9cf08d6d9ae8a500eaf0c83d4724`

Type:

```lean
∀ {α : Sort u} {a a' : α}, HEq a a' → Eq a a'
```

Fully explicit type:

```lean
∀ {α : Sort u} {a a' : α} (h : @HEq.{u} α a α a'), @Eq.{u} α a a'
```

### D132: `PProd.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `10`
- Semantic SHA-256: `77a288dd932e98f780ede81f87af6b4ae802bc357db102e11bc037200b5d6eb0`

Type:

```lean
{α : Sort u} → {β : Sort v} → α → β → PProd α β
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → (fst : α) → (snd : β) → PProd.{u, v} α β
```

### D133: `PUnit.unit`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `10`
- Semantic SHA-256: `50562948622e7272ab5a2c0f9fcc2a46933f516e02ad00c5deddc196666390b0`

Type:

```lean
PUnit
```

Fully explicit type:

```lean
PUnit.{u}
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

### `HighamBench.P05Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P05Definitions.lean`
SHA-256: `1a399e16e2453fdb7b05d46e0f4e348e6c74ccf10944ed28b411722811f7875a`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- The finite square matrix product used in P05's LU and Cholesky bounds. -/
noncomputable def p05MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix transpose in P05's finite-index notation. -/
noncomputable def p05Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A j i

/-- The componentwise absolute product `|A||B|` used by both factorization
backward-error bounds in P05. -/
noncomputable def p05AbsMatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |A i k| * |B k j|

/-- A finite radix format interface sufficient to state P05 Lemma 4.1's
round-to-nearest execution. `safeRange` excludes underflow and overflow for an
exact operation result. -/
structure P05FiniteRoundToNearestFormat where
  radix : ℕ
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  radix_ge_two : 2 ≤ radix
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent < maxExponent
  representable : ℝ → Prop
  representable_finite : Set.Finite {x | representable x}
  safeRange : ℝ → Prop
  round : ℝ → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_scale :
    unitRoundoff * (2 * (radix : ℝ) ^ (precision - 1)) = 1
  zero_representable : representable 0
  one_representable : representable 1
  round_representable : ∀ x, safeRange x → representable (round x)
  round_nearest : ∀ x, safeRange x → ∀ z, representable z →
    |x - round x| ≤ |x - z|
  round_exact : ∀ x, representable x → round x = x

/-- A binary tree encoding an arbitrary pairwise evaluation order for a
nonempty finite sum. -/
inductive P05SumTree : ℕ → Type
  | leaf : P05SumTree 1
  | node {m n : ℕ} : P05SumTree m → P05SumTree n → P05SumTree (m + n)

/-- Evaluation of a P05 summation tree, rounding at every internal addition. -/
noncomputable def p05SumTreeEval
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : ℝ :=
  match tree with
  | .leaf => v ⟨0, by norm_num⟩
  | .node left right =>
      fmt.round
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

/-- Every exact internal addition in a tree lies in the format's range, which
is the paper's no-underflow/no-overflow requirement for summation. -/
def p05SumTreeSafe
    (fmt : P05FiniteRoundToNearestFormat) {n : ℕ}
    (tree : P05SumTree n) (v : Fin n → ℝ) : Prop :=
  match tree with
  | .leaf => fmt.representable (v ⟨0, by norm_num⟩)
  | .node left right =>
      p05SumTreeSafe fmt left (fun i => v (Fin.castAdd _ i)) ∧
      p05SumTreeSafe fmt right (fun i => v (Fin.natAdd _ i)) ∧
      fmt.safeRange
        (p05SumTreeEval fmt left (fun i => v (Fin.castAdd _ i)) +
          p05SumTreeEval fmt right (fun i => v (Fin.natAdd _ i)))

/-- Rounded products appearing in the computed numerator of P05 Lemma 4.1. -/
noncomputable def p05RoundedProducts {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => fmt.round (a i * b i)

/-- The summands `c,-fl(a₁b₁),...,-fl(aₘbₘ)` supplied to an
arbitrary summation tree in P05 Lemma 4.1, where the paper's `k=m+1`. -/
noncomputable def p05Lemma41Summands {m : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (a b : Fin m → ℝ) (c : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases c (fun i => -p05RoundedProducts fmt a b i)

/-- The two perturbable source families in Lemma 4.1. The protected input `c`
is deliberately absent. -/
noncomputable def p05BackwardSource {m : ℕ}
    (computedProduct : ℝ) (products : Fin m → ℝ) :
    Option (Fin m) → ℝ
  | none => computedProduct
  | some i => products i

/-- A complete finite execution certificate for P05 Lemma 4.1. The tree and
permutation encode every permitted summation order. Product, addition, and
division range fields state the absence of underflow and overflow. The two
residual fields are exactly the consequences of Theorem 3.1 and Corollary 3.2
used by the paper to construct Lemma 4.1's coefficients; neither field contains
those coefficients or the target conclusion. -/
structure P05Lemma41Run (m : ℕ) where
  format : P05FiniteRoundToNearestFormat
  a : Fin m → ℝ
  b : Fin m → ℝ
  bK : ℝ
  c : ℝ
  a_representable : ∀ i, format.representable (a i)
  b_representable : ∀ i, format.representable (b i)
  bK_representable : format.representable bK
  c_representable : format.representable c
  bK_nonzero : bK ≠ 0
  product_safe : ∀ i, format.safeRange (a i * b i)
  tree : P05SumTree (m + 1)
  order : Equiv.Perm (Fin (m + 1))
  tree_safe : p05SumTreeSafe format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator : ℝ
  numerator_eq : numerator = p05SumTreeEval format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  yHat : ℝ
  no_division_when_unit : bK = 1 → yHat = numerator
  division_safe : bK ≠ 1 → format.safeRange (numerator / bK)
  rounded_division : bK ≠ 1 → yHat = format.round (numerator / bK)
  general_residual_bound :
    |(c - ∑ i : Fin m, a i * b i) - bK * yHat| ≤
      ((m + 1 : ℕ) : ℝ) * format.unitRoundoff *
        (|bK * yHat| + ∑ i : Fin m, |a i * b i|)
  unit_residual_bound : bK = 1 →
    |(c - ∑ i : Fin m, a i * b i) - yHat| ≤
      (m : ℝ) * format.unitRoundoff *
        (|yHat| + ∑ i : Fin m, |a i * b i|)

/-- Exact rectangular matrix multiplication for P05 Theorem 4.2. -/
noncomputable def p05RectMatMul {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, L i k * U k j

/-- The componentwise absolute product `|L_hat||U_hat|` in Theorem 4.2. -/
noncomputable def p05RectAbsMatMul {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |L i k| * |U k j|

/-- Embed a Doolittle pivot-row index into the rectangular row index. -/
def p05RectRow {m n : ℕ} (hmn : n ≤ m) (k : Fin n) : Fin m :=
  Fin.castLE hmn k

/-- Embed an index strictly preceding Doolittle stage `k` into `Fin n`. -/
def p05PrefixIndex {n : ℕ} (k : Fin n) (s : Fin k.val) : Fin n :=
  ⟨s.val, lt_trans s.isLt k.isLt⟩

/-- The exact dot product over entries strictly preceding Doolittle stage `k`. -/
noncomputable def p05DoolittlePrefixDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin k.val, L i (p05PrefixIndex k s) * U (p05PrefixIndex k s) j

/-- The corresponding absolute-value prefix dot product. -/
noncomputable def p05DoolittlePrefixAbsDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L i (p05PrefixIndex k s)| * |U (p05PrefixIndex k s) j|

/-- The exact local product through stage `k`, matching the sums in (4.3). -/
noncomputable def p05DoolittleThroughPivotDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  p05DoolittlePrefixDot L U i j k + L i k * U k j

/-- The absolute local product through stage `k`, matching the right sides of
equations (4.3a) and (4.3b). -/
noncomputable def p05DoolittleThroughPivotAbsDot {m n : ℕ}
    (L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (j k : Fin n) : ℝ :=
  p05DoolittlePrefixAbsDot L U i j k + |L i k| * |U k j|

/-- One completed upper-row Doolittle evaluation at stage `k`. The nested
Lemma 4.1 run computes `U_hat[k,j]` from the protected input `A[k,j]`, the
already computed prefix products, and unit denominator. -/
structure P05DoolittleUpperEntry {m n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat) (hmn : n ≤ m)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (k j : Fin n) where
  execution : P05Lemma41Run k.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ s,
    execution.a s = L (p05RectRow hmn k) (p05PrefixIndex k s)
  right_input_eq : ∀ s,
    execution.b s = U (p05PrefixIndex k s) j
  denominator_eq : execution.bK = 1
  protected_input_eq : execution.c = A (p05RectRow hmn k) j
  computed_output_eq : execution.yHat = U k j

/-- One completed below-diagonal Doolittle evaluation at stage `k`. The nested
Lemma 4.1 run computes `L_hat[i,k]` after division by the computed pivot
`U_hat[k,k]`. -/
structure P05DoolittleLowerEntry {m n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A L : Fin m → Fin n → ℝ) (U : Fin n → Fin n → ℝ)
    (i : Fin m) (k : Fin n) where
  execution : P05Lemma41Run k.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ s,
    execution.a s = L i (p05PrefixIndex k s)
  right_input_eq : ∀ s,
    execution.b s = U (p05PrefixIndex k s) k
  denominator_eq : execution.bK = U k k
  protected_input_eq : execution.c = A i k
  computed_output_eq : execution.yHat = L i k

/-- A completed rectangular floating-point Doolittle run used in the proof of
P05 Theorem 4.2. Every stored upper and lower entry has its own arbitrary-order,
range-certified Lemma 4.1 execution. Thus completion, round-to-nearest
arithmetic, and the absence of underflow and overflow are explicit without
storing a Doolittle-specific local estimate or the final matrix bound. -/
structure P05DoolittleRun (m n : ℕ) where
  format : P05FiniteRoundToNearestFormat
  rows_ge_columns : n ≤ m
  columns_pos : 0 < n
  A : Fin m → Fin n → ℝ
  LHat : Fin m → Fin n → ℝ
  UHat : Fin n → Fin n → ℝ
  A_representable : ∀ i j, format.representable (A i j)
  LHat_representable : ∀ i j, format.representable (LHat i j)
  UHat_representable : ∀ i j, format.representable (UHat i j)
  LHat_diag : ∀ k : Fin n, LHat (p05RectRow rows_ge_columns k) k = 1
  LHat_upper_zero : ∀ i j, i.val < j.val → LHat i j = 0
  UHat_lower_zero : ∀ i j, j.val < i.val → UHat i j = 0
  upper_entry : ∀ k j, k.val ≤ j.val →
    P05DoolittleUpperEntry format rows_ge_columns A LHat UHat k j
  lower_entry : ∀ i k, k.val < i.val →
    P05DoolittleLowerEntry format A LHat UHat i k

/-- A range-certified execution of P05 Lemma 4.3's rounded square-root
expression with `m` product terms. The residual field is the generic scalar
consequence inherited from Corollary 3.2, before any Cholesky entry is
substituted. -/
structure P05Lemma43Run (m : ℕ) where
  format : P05FiniteRoundToNearestFormat
  a : Fin m → ℝ
  b : Fin m → ℝ
  c : ℝ
  a_representable : ∀ i, format.representable (a i)
  b_representable : ∀ i, format.representable (b i)
  c_representable : format.representable c
  product_safe : ∀ i, format.safeRange (a i * b i)
  tree : P05SumTree (m + 1)
  order : Equiv.Perm (Fin (m + 1))
  tree_safe : p05SumTreeSafe format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator : ℝ
  numerator_eq : numerator = p05SumTreeEval format tree
    (fun i => p05Lemma41Summands format a b c (order i))
  numerator_nonneg : 0 ≤ numerator
  sqrt_safe : format.safeRange (Real.sqrt numerator)
  yHat : ℝ
  rounded_sqrt : yHat = format.round (Real.sqrt numerator)
  yHat_nonneg : 0 ≤ yHat
  sqrt_residual_bound :
    |(c - ∑ i : Fin m, a i * b i) - yHat ^ 2| ≤
      ((m + 2 : ℕ) : ℝ) * format.unitRoundoff *
        (|yHat ^ 2| + ∑ i : Fin m, |a i * b i|)

/-- Exact prefix Gram entry used by the conventional Cholesky algorithm. -/
noncomputable def p05CholeskyPrefixDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k : Fin i.val,
    R (p05PrefixIndex i k) i * R (p05PrefixIndex i k) j

/-- Absolute-value counterpart of the Cholesky prefix Gram entry. -/
noncomputable def p05CholeskyPrefixAbsDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k : Fin i.val,
    |R (p05PrefixIndex i k) i| * |R (p05PrefixIndex i k) j|

/-- Cholesky's Gram entry through row `i`, including the newly computed term. -/
noncomputable def p05CholeskyThroughDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  p05CholeskyPrefixDot R i j + R i i * R i j

/-- Absolute Cholesky Gram entry through row `i`. -/
noncomputable def p05CholeskyThroughAbsDot {n : ℕ}
    (R : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  p05CholeskyPrefixAbsDot R i j + |R i i| * |R i j|

/-- One computed off-diagonal entry in a conventional Cholesky column. -/
structure P05CholeskyOffDiagonalEntry {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A R : Fin n → Fin n → ℝ) (i j : Fin n) where
  execution : P05Lemma41Run i.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ k,
    execution.a k = R (p05PrefixIndex i k) i
  right_input_eq : ∀ k,
    execution.b k = R (p05PrefixIndex i k) j
  denominator_eq : execution.bK = R i i
  protected_input_eq : execution.c = A i j
  computed_output_eq : execution.yHat = R i j

/-- One computed diagonal square-root entry in a conventional Cholesky column. -/
structure P05CholeskyDiagonalEntry {n : ℕ}
    (fmt : P05FiniteRoundToNearestFormat)
    (A R : Fin n → Fin n → ℝ) (j : Fin n) where
  execution : P05Lemma43Run j.val
  format_eq : execution.format = fmt
  left_input_eq : ∀ k,
    execution.a k = R (p05PrefixIndex j k) j
  right_input_eq : ∀ k,
    execution.b k = R (p05PrefixIndex j k) j
  protected_input_eq : execution.c = A j j
  computed_output_eq : execution.yHat = R j j

/-- A completed conventional floating-point Cholesky execution for P05
Theorem 4.4. Each column entry is linked to its arbitrary-order, range-certified
subtraction/division or subtraction/square-root execution. -/
structure P05CholeskyRun (n : ℕ) where
  format : P05FiniteRoundToNearestFormat
  dimension_pos : 0 < n
  A : Fin n → Fin n → ℝ
  RHat : Fin n → Fin n → ℝ
  A_representable : ∀ i j, format.representable (A i j)
  RHat_representable : ∀ i j, format.representable (RHat i j)
  A_symmetric : ∀ i j, A i j = A j i
  RHat_lower_zero : ∀ i j, j.val < i.val → RHat i j = 0
  off_diagonal_entry : ∀ i j, i.val < j.val →
    P05CholeskyOffDiagonalEntry format A RHat i j
  diagonal_entry : ∀ j,
    P05CholeskyDiagonalEntry format A RHat j

end HighamBench
```
