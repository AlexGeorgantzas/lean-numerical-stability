# Declaration dossier for P04-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p04_t1_chained_rounding_factor
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) :
    ∃ alpha beta : Fin n → ℝ,
      run.computed = ∑ i : Fin n,
        run.x i * run.y i * (1 + alpha i) * (1 + beta i) ∧
      (∀ i, |alpha i| ≤
        gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q) ∧
      (∀ i, |beta i| ≤ gamma run.uBar n) ∧
      |p04Dot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff
            (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
            run.uBar q n *
          p04AbsDot run.x run.y ∧
      (run.rightToLeft →
        (∀ i, |beta i| ≤ gamma run.uBar (q + b - 1)) ∧
        |p04Dot run.x run.y - run.computed| ≤
          p04BlockFmaCoeff
              (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
              run.uBar q (q + b - 1) *
            p04AbsDot run.x run.y) ∧
      (run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
        (∀ i, alpha i = 0) ∧
        |p04Dot run.x run.y - run.computed| ≤
          gamma run.uBar n * p04AbsDot run.x run.y)
```

## Elaborated target type

```lean
∀ {n b q : Nat} (run : HighamBench.P04BlockFmaDotRun n b q),
  Exists fun alpha =>
    Exists fun beta =>
      And
        (Eq run.computed
          (Finset.univ.sum fun i =>
            instHMul.hMul (instHMul.hMul (instHMul.hMul (run.x i) (run.y i)) (instHAdd.hAdd 1 (alpha i)))
              (instHAdd.hAdd 1 (beta i))))
        (And
          (∀ (i : Fin n),
            Real.instLE.le (abs (alpha i))
              (HighamBench.gamma (HighamBench.p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q))
          (And (∀ (i : Fin n), Real.instLE.le (abs (beta i)) (HighamBench.gamma run.uBar n))
            (And
              (Real.instLE.le (abs (instHSub.hSub (HighamBench.p04Dot run.x run.y) run.computed))
                (instHMul.hMul
                  (HighamBench.p04BlockFmaCoeff (HighamBench.p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
                    run.uBar q n)
                  (HighamBench.p04AbsDot run.x run.y)))
              (And
                (run.rightToLeft →
                  And
                    (∀ (i : Fin n),
                      Real.instLE.le (abs (beta i)) (HighamBench.gamma run.uBar (instHSub.hSub (instHAdd.hAdd q b) 1)))
                    (Real.instLE.le (abs (instHSub.hSub (HighamBench.p04Dot run.x run.y) run.computed))
                      (instHMul.hMul
                        (HighamBench.p04BlockFmaCoeff (HighamBench.p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
                          run.uBar q (instHSub.hSub (instHAdd.hAdd q b) 1))
                        (HighamBench.p04AbsDot run.x run.y))))
                (And (Real.instLE.le run.uOut run.uFma) (Eq run.uBar run.uFma) →
                  And (∀ (i : Fin n), Eq (alpha i) 0)
                    (Real.instLE.le (abs (instHSub.hSub (HighamBench.p04Dot run.x run.y) run.computed))
                      (instHMul.hMul (HighamBench.gamma run.uBar n) (HighamBench.p04AbsDot run.x run.y))))))))
```

## Fully explicit elaborated target type

```lean
∀ {n b q : Nat} (run : HighamBench.P04BlockFmaDotRun n b q),
  @Exists.{1} (Fin n → Real) fun (alpha : Fin n → Real) =>
    @Exists.{1} (Fin n → Real) fun (beta : Fin n → Real) =>
      And
        (@Eq.{1} Real (@HighamBench.P04BlockFmaDotRun.computed n b q run)
          (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin n) (Fin.fintype n))
            fun (i : Fin n) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HighamBench.P04BlockFmaDotRun.x n b q run i) (@HighamBench.P04BlockFmaDotRun.y n b q run i))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (alpha i)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (beta i))))
        (And
          (∀ (i : Fin n),
            @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (alpha i))
              (HighamBench.gamma
                (HighamBench.p04EffectiveFmaRoundoff (@HighamBench.P04BlockFmaDotRun.uBar n b q run)
                  (@HighamBench.P04BlockFmaDotRun.uFma n b q run) (@HighamBench.P04BlockFmaDotRun.uOut n b q run))
                q))
          (And
            (∀ (i : Fin n),
              @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (beta i))
                (HighamBench.gamma (@HighamBench.P04BlockFmaDotRun.uBar n b q run) n))
            (And
              (@LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HighamBench.p04Dot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                      (@HighamBench.P04BlockFmaDotRun.y n b q run))
                    (@HighamBench.P04BlockFmaDotRun.computed n b q run)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (HighamBench.p04BlockFmaCoeff
                    (HighamBench.p04EffectiveFmaRoundoff (@HighamBench.P04BlockFmaDotRun.uBar n b q run)
                      (@HighamBench.P04BlockFmaDotRun.uFma n b q run) (@HighamBench.P04BlockFmaDotRun.uOut n b q run))
                    (@HighamBench.P04BlockFmaDotRun.uBar n b q run) q n)
                  (@HighamBench.p04AbsDot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                    (@HighamBench.P04BlockFmaDotRun.y n b q run))))
              (And
                (@HighamBench.P04BlockFmaDotRun.rightToLeft n b q run →
                  And
                    (∀ (i : Fin n),
                      @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (beta i))
                        (HighamBench.gamma (@HighamBench.P04BlockFmaDotRun.uBar n b q run)
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q b)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HighamBench.p04Dot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                            (@HighamBench.P04BlockFmaDotRun.y n b q run))
                          (@HighamBench.P04BlockFmaDotRun.computed n b q run)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (HighamBench.p04BlockFmaCoeff
                          (HighamBench.p04EffectiveFmaRoundoff (@HighamBench.P04BlockFmaDotRun.uBar n b q run)
                            (@HighamBench.P04BlockFmaDotRun.uFma n b q run)
                            (@HighamBench.P04BlockFmaDotRun.uOut n b q run))
                          (@HighamBench.P04BlockFmaDotRun.uBar n b q run) q
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q b)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@HighamBench.p04AbsDot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                          (@HighamBench.P04BlockFmaDotRun.y n b q run)))))
                (And
                    (@LE.le.{0} Real Real.instLE (@HighamBench.P04BlockFmaDotRun.uOut n b q run)
                      (@HighamBench.P04BlockFmaDotRun.uFma n b q run))
                    (@Eq.{1} Real (@HighamBench.P04BlockFmaDotRun.uBar n b q run)
                      (@HighamBench.P04BlockFmaDotRun.uFma n b q run)) →
                  And
                    (∀ (i : Fin n),
                      @Eq.{1} Real (alpha i)
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                    (@LE.le.{0} Real Real.instLE
                      (@abs.{0} Real Real.lattice Real.instAddGroup
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HighamBench.p04Dot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                            (@HighamBench.P04BlockFmaDotRun.y n b q run))
                          (@HighamBench.P04BlockFmaDotRun.computed n b q run)))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (HighamBench.gamma (@HighamBench.P04BlockFmaDotRun.uBar n b q run) n)
                        (@HighamBench.p04AbsDot n (@HighamBench.P04BlockFmaDotRun.x n b q run)
                          (@HighamBench.P04BlockFmaDotRun.y n b q run)))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P04Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P04Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P04BlockFmaDotRun`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `4944bca2329eb454982d0814cc41eeb43369f287267aa02482bb780f17148ce2`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(n b q : Nat) → Type
```

### D002: `HighamBench.P04BlockFmaDotRun.computed`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `68274bb7b767f2c78147c09db9a7940181c824464edcb43cd90180f33cc81fff`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.7
```

### D003: `HighamBench.P04BlockFmaDotRun.rightToLeft`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5e7d45f7d624c020e85587b3bacf967c8ec32b5075b6e9b5f620e2588b97c913`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Prop
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.22
```

### D004: `HighamBench.P04BlockFmaDotRun.uBar`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b99e276e691b4500ceeb6b5bcb43acf765276e074303e40d9e702fc5baf81987`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.8
```

### D005: `HighamBench.P04BlockFmaDotRun.uFma`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3a825ac0b9e40e1c143a121e7844f5f517d063777b64d58035e2b5b44655f11e`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.9
```

### D006: `HighamBench.P04BlockFmaDotRun.uOut`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f2c815e3c136dfcdfcb4df37ea528c4bac1afbadaf14a34ee343171534b37d84`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.10
```

### D007: `HighamBench.P04BlockFmaDotRun.x`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `665bcf6249dab190671979e68d52cdbb7d2e2e0c136fc3a008863109cc1acb14`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.5
```

### D008: `HighamBench.P04BlockFmaDotRun.y`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `6b23d33b452c454597fdad9edd78c3242433bbc566deda310b2791ad4f5f64b3`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.6
```

### D009: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `f15d03b13b3e456f86c0d1afbecf5720b016231e8755a130fe4ff7bf44902bf0`

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

### D010: `HighamBench.p04AbsDot`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `d8a32f6c2662831e05b7cf39519a27b4464ac57255ac56d765d4907c9c817a35`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (abs (x i)) (abs (y i))
```

### D011: `HighamBench.p04BlockFmaCoeff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7829a2958439fc05b0c2715ff1c5b4140cff6f33dd06568386434b5f6a25252a`

Type:

```lean
Real → Real → Nat → Nat → Real
```

Fully explicit type:

```lean
(uFma u : Real) → (q n : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun uFma u q n =>
  instHAdd.hAdd (instHAdd.hAdd (HighamBench.gamma uFma q) (HighamBench.gamma u n))
    (instHMul.hMul (HighamBench.gamma uFma q) (HighamBench.gamma u n))
```

### D012: `HighamBench.p04Dot`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `5cde2e20f0e54520e4d8828b713ee858807cf2c4f334c9b79756cf0d0d8f4f1b`

Type:

```lean
{n : Nat} → (Fin n → Real) → (Fin n → Real) → Real
```

Fully explicit type:

```lean
{n : Nat} → (x y : Fin n → Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} x y => Finset.univ.sum fun i => instHMul.hMul (x i) (y i)
```

### D013: `HighamBench.p04EffectiveFmaRoundoff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6f93bd3a032348a15ab4816595eda68a279e901560d58e515296e667cdd7f14f`

Type:

```lean
Real → Real → Real → Real
```

Fully explicit type:

```lean
(uBar uFma uOut : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun uBar uFma uOut => ite (Real.instLT.lt uFma uOut) uOut (ite (Real.instLE.le uFma uBar) 0 uFma)
```

### D014: `HighamBench.P04BlockFmaDotRun.mk`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `32243ab14157c86eecadd351f6ba3ae9782b5c14a8ca5b83590303ceb3837a90`

Type:

```lean
{n b q : Nat} →
  instLTNat.lt 0 n →
    instLTNat.lt 0 b →
      instLTNat.lt 0 q →
        Eq n (instHMul.hMul q b) →
          (x y : Fin n → Real) →
            (computed uBar uFma uOut : Real) →
              Real.instLE.le 0 uBar →
                Real.instLE.le 0 uFma →
                  Real.instLE.le 0 uOut →
                    Real.instLE.le uBar uFma →
                      HighamBench.GammaValid (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q →
                        HighamBench.GammaValid uBar n →
                          (alpha beta : Fin n → Real) →
                            Eq computed
                                (Finset.univ.sum fun i =>
                                  instHMul.hMul (instHMul.hMul (instHMul.hMul (x i) (y i)) (instHAdd.hAdd 1 (alpha i)))
                                    (instHAdd.hAdd 1 (beta i))) →
                              (∀ (i : Fin n),
                                  Real.instLE.le (abs (alpha i))
                                    (HighamBench.gamma (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q)) →
                                (∀ (i : Fin n), Real.instLE.le (abs (beta i)) (HighamBench.gamma uBar n)) →
                                  (rightToLeft : Prop) →
                                    (rightToLeft → HighamBench.GammaValid uBar (instHSub.hSub (instHAdd.hAdd q b) 1)) →
                                      (rightToLeft →
                                          ∀ (i : Fin n),
                                            Real.instLE.le (abs (beta i))
                                              (HighamBench.gamma uBar (instHSub.hSub (instHAdd.hAdd q b) 1))) →
                                        HighamBench.P04BlockFmaDotRun n b q
```

Fully explicit type:

```lean
{n b q : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (block_size_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b) →
      (block_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) →
        (dimension_eq : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
          (x y : Fin n → Real) →
            (computed uBar uFma uOut : Real) →
              (uBar_nonneg :
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uBar) →
                (uFma_nonneg :
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uFma) →
                  (uOut_nonneg :
                      @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uOut) →
                    (uBar_le_uFma : @LE.le.{0} Real Real.instLE uBar uFma) →
                      (effective_gamma_valid :
                          HighamBench.GammaValid (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q) →
                        (internal_gamma_valid : HighamBench.GammaValid uBar n) →
                          (alpha beta : Fin n → Real) →
                            (algorithm3_1_factorization :
                                @Eq.{1} Real computed
                                  (@Finset.sum.{0, 0} (Fin n) Real Real.instAddCommMonoid
                                    (@Finset.univ.{0} (Fin n) (Fin.fintype n)) fun (i : Fin n) =>
                                    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (x i)
                                          (y i))
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                          (alpha i)))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                        (beta i)))) →
                              (alpha_bound :
                                  ∀ (i : Fin n),
                                    @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (alpha i))
                                      (HighamBench.gamma (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q)) →
                                (beta_bound :
                                    ∀ (i : Fin n),
                                      @LE.le.{0} Real Real.instLE
                                        (@abs.{0} Real Real.lattice Real.instAddGroup (beta i))
                                        (HighamBench.gamma uBar n)) →
                                  (rightToLeft : Prop) →
                                    (right_to_left_gamma_valid :
                                        rightToLeft →
                                          HighamBench.GammaValid uBar
                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q b)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                      (right_to_left_beta_bound :
                                          rightToLeft →
                                            ∀ (i : Fin n),
                                              @LE.le.{0} Real Real.instLE
                                                (@abs.{0} Real Real.lattice Real.instAddGroup (beta i))
                                                (HighamBench.gamma uBar
                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                                                      b)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                        HighamBench.P04BlockFmaDotRun n b q
```

### D015: `HighamBench.GammaValid`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `651ef903a8d9a3c8f539284f6c70325cebe6e199aad808cb56d9123f31e258c9`

Type:

```lean
Real → Nat → Prop
```

Fully explicit type:

```lean
(u : Real) → (n : Nat) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun u n => Real.instLT.lt (instHMul.hMul n.cast u) 1
```

### D016: `And`

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

### D017: `Eq`

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

### D018: `Exists`

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

### D019: `Fin`

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

### D020: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D021: `Finset.sum`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D022: `Finset.univ`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D023: `HAdd.hAdd`

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

### D024: `HMul.hMul`

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

### D025: `HSub.hSub`

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

### D026: `LE.le`

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

### D027: `Nat`

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

### D028: `OfNat.ofNat`

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

### D029: `One.toOfNat1`

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

### D030: `Real`

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

### D031: `Real.instAdd`

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

### D032: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D033: `Real.instAddGroup`

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

### D034: `Real.instLE`

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

### D035: `Real.instMul`

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

### D036: `Real.instOne`

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

### D037: `Real.instSub`

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

### D038: `Real.instZero`

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

### D039: `Real.lattice`

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

### D040: `Zero.toOfNat0`

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

### D041: `abs`

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

### D042: `instAddNat`

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

### D043: `instHAdd`

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

### D044: `instHMul`

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

### D045: `instHSub`

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

### D046: `instOfNatNat`

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

### D047: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D048: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D049: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D050: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D051: `Nat.cast`

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

### D052: `Real.decidableLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5ad021b20f1dc17f5e341bc278e2f4c546324ba782b37f6f6690b632da927ead`

Type:

```lean
(a b : Real) → Decidable (Real.instLE.le a b)
```

Fully explicit type:

```lean
(a b : Real) → Decidable (@LE.le.{0} Real Real.instLE a b)
```

Definition body (one-level semantic boundary):

```lean
fun a b => inferInstance
```

### D053: `Real.decidableLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D054: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D055: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D056: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D057: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D058: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `3029bae29d2d16b5aeb879ad3c12a1b3c4e78998083bf1ab4614942fafdece0e`

Type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → α → α → α
```

Fully explicit type:

```lean
{α : Sort u} → (c : Prop) → [h : Decidable c] → (t e : α) → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t
```

### D059: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D060: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `15abc50804fa78aecc5a807f82f13a6b67bcdff9061558426471fc4b606841aa`

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
