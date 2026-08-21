# Declaration dossier for P04-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p04_t2_mixed_input_product_bound
    {m n t b1 b b2 p q r : ℕ}
    (run : P04MixedInputMatMulRun m n t b1 b b2 p q r) :
    ∀ i j,
      |run.computed i j - p04RectMatMul run.A run.B i j| ≤
        (2 * run.uLow + run.uLow ^ 2 +
            p04BlockFmaCoeff
                (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
                run.uBar q n * (1 + run.uLow) ^ 2) *
          p04AbsRectMatMul run.A run.B i j
```

## Elaborated target type

```lean
∀ {m n t b1 b b2 p q r : Nat} (run : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) (i : Fin m) (j : Fin t),
  Real.instLE.le (abs (instHSub.hSub (run.computed i j) (HighamBench.p04RectMatMul run.A run.B i j)))
    (instHMul.hMul
      (instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 run.uLow) (instHPow.hPow run.uLow 2))
        (instHMul.hMul
          (HighamBench.p04BlockFmaCoeff (HighamBench.p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) run.uBar q n)
          (instHPow.hPow (instHAdd.hAdd 1 run.uLow) 2)))
      (HighamBench.p04AbsRectMatMul run.A run.B i j))
```

## Fully explicit elaborated target type

```lean
∀ {m n t b1 b b2 p q r : Nat} (run : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) (i : Fin m) (j : Fin t),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HighamBench.P04MixedInputMatMulRun.computed m n t b1 b b2 p q r run i j)
        (@HighamBench.p04RectMatMul m n t (@HighamBench.P04MixedInputMatMulRun.A m n t b1 b b2 p q r run)
          (@HighamBench.P04MixedInputMatMulRun.B m n t b1 b b2 p q r run) i j)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@HighamBench.P04MixedInputMatMulRun.uLow m n t b1 b b2 p q r run))
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HighamBench.P04MixedInputMatMulRun.uLow m n t b1 b b2 p q r run)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (HighamBench.p04BlockFmaCoeff
            (HighamBench.p04EffectiveFmaRoundoff (@HighamBench.P04MixedInputMatMulRun.uBar m n t b1 b b2 p q r run)
              (@HighamBench.P04MixedInputMatMulRun.uFma m n t b1 b b2 p q r run)
              (@HighamBench.P04MixedInputMatMulRun.uOut m n t b1 b b2 p q r run))
            (@HighamBench.P04MixedInputMatMulRun.uBar m n t b1 b b2 p q r run) q n)
          (@HPow.hPow.{0, 0, 0} Real Nat Real (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@HighamBench.P04MixedInputMatMulRun.uLow m n t b1 b b2 p q r run))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
      (@HighamBench.p04AbsRectMatMul m n t (@HighamBench.P04MixedInputMatMulRun.A m n t b1 b b2 p q r run)
        (@HighamBench.P04MixedInputMatMulRun.B m n t b1 b b2 p q r run) i j))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P04Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P04Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P04MixedInputMatMulRun`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `8ae2ef854acc321e6e6d95641cb08a5763d64700fdd30848ee345c6ac8224cc4`

Type:

```lean
Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(m n t b1 b b2 p q r : Nat) → Type
```

### D002: `HighamBench.P04MixedInputMatMulRun.A`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `18fb2b9b5e1109288d30e0f1ad3e88df54732ee32f4abe36b7f4630566aeec55`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Fin m → Fin n → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Fin m → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.13
```

### D003: `HighamBench.P04MixedInputMatMulRun.B`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fe3b8d54c52db95212f7a1127fee1a100aac5e464b83cbdb822154f64244ec0e`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Fin n → Fin t → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Fin n → Fin t → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.14
```

### D004: `HighamBench.P04MixedInputMatMulRun.computed`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2db83e67ed0f4b343886dc530f2ae659f575d383674a57ca1710e8db391acef9`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Fin m → Fin t → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Fin m → Fin t → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.19
```

### D005: `HighamBench.P04MixedInputMatMulRun.uBar`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `b816d4fd064e18635320626f03a49294cf4c38199b11b5f6c7d723fa6b003be3`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.21
```

### D006: `HighamBench.P04MixedInputMatMulRun.uFma`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `33648da71c8359e6873bd0fce638510cf06a320fcfc721f68e6f574f2a2844ab`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.22
```

### D007: `HighamBench.P04MixedInputMatMulRun.uLow`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `59e825914c4e8911fb4e859ae2c7b8f64a1e1650aa1ad95e689f30605bd814d4`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.20
```

### D008: `HighamBench.P04MixedInputMatMulRun.uOut`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `95971c7200cb28ed38c6d06ccc2e449f4af364b37c2eebe77b650f46e5684826`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Real
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.23
```

### D009: `HighamBench.p04AbsRectMatMul`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2d006bb6e8aec54f4309d854f49b6dd5f9cd3ea823ff13b4597fb00c73871b66`

Type:

```lean
{m n t : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin t → Real) → Fin m → Fin t → Real
```

Fully explicit type:

```lean
{m n t : Nat} → (A : Fin m → Fin n → Real) → (B : Fin n → Fin t → Real) → Fin m → Fin t → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n t} A B i j => Finset.univ.sum fun k => instHMul.hMul (abs (A i k)) (abs (B k j))
```

### D010: `HighamBench.p04BlockFmaCoeff`

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

### D011: `HighamBench.p04EffectiveFmaRoundoff`

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

### D012: `HighamBench.p04RectMatMul`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `20407f56205320bfb1147fc957c5423309a7133f4d19d5a22e997c76cf5939f0`

Type:

```lean
{m n t : Nat} → (Fin m → Fin n → Real) → (Fin n → Fin t → Real) → Fin m → Fin t → Real
```

Fully explicit type:

```lean
{m n t : Nat} → (A : Fin m → Fin n → Real) → (B : Fin n → Fin t → Real) → Fin m → Fin t → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n t} A B i j => Finset.univ.sum fun k => instHMul.hMul (A i k) (B k j)
```

### D013: `HighamBench.P04MixedInputMatMulRun.mk`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `89dd9106be74d15e03530c9edc5123b348054e085b30aab6d6552a47ed9e4a40`

Type:

```lean
{m n t b1 b b2 p q r : Nat} →
  instLTNat.lt 0 m →
    instLTNat.lt 0 n →
      instLTNat.lt 0 t →
        instLTNat.lt 0 b1 →
          instLTNat.lt 0 b →
            instLTNat.lt 0 b2 →
              instLTNat.lt 0 p →
                instLTNat.lt 0 q →
                  instLTNat.lt 0 r →
                    Eq m (instHMul.hMul p b1) →
                      Eq n (instHMul.hMul q b) →
                        Eq t (instHMul.hMul r b2) →
                          (A : Fin m → Fin n → Real) →
                            (B : Fin n → Fin t → Real) →
                              (convertedA : Fin m → Fin n → Real) →
                                (convertedB : Fin n → Fin t → Real) →
                                  (deltaA : Fin m → Fin n → Real) →
                                    (deltaB : Fin n → Fin t → Real) →
                                      (computed : Fin m → Fin t → Real) →
                                        (uLow uBar uFma uOut : Real) →
                                          Real.instLE.le 0 uLow →
                                            Real.instLE.le 0 uBar →
                                              Real.instLE.le 0 uFma →
                                                Real.instLE.le 0 uOut →
                                                  Real.instLE.le uBar uFma →
                                                    HighamBench.GammaValid
                                                        (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q →
                                                      HighamBench.GammaValid uBar n →
                                                        (∀ (i : Fin m) (k : Fin n),
                                                            Eq (convertedA i k) (instHAdd.hAdd (A i k) (deltaA i k))) →
                                                          (∀ (k : Fin n) (j : Fin t),
                                                              Eq (convertedB k j)
                                                                (instHAdd.hAdd (B k j) (deltaB k j))) →
                                                            (∀ (i : Fin m) (k : Fin n),
                                                                Real.instLE.le (abs (deltaA i k))
                                                                  (instHMul.hMul uLow (abs (A i k)))) →
                                                              (∀ (k : Fin n) (j : Fin t),
                                                                  Real.instLE.le (abs (deltaB k j))
                                                                    (instHMul.hMul uLow (abs (B k j)))) →
                                                                (alpha beta : Fin m → Fin t → Fin n → Real) →
                                                                  (∀ (i : Fin m) (j : Fin t),
                                                                      Eq (computed i j)
                                                                        (Finset.univ.sum fun k =>
                                                                          instHMul.hMul
                                                                            (instHMul.hMul
                                                                              (instHMul.hMul (convertedA i k)
                                                                                (convertedB k j))
                                                                              (instHAdd.hAdd 1 (alpha i j k)))
                                                                            (instHAdd.hAdd 1 (beta i j k)))) →
                                                                    (∀ (i : Fin m) (j : Fin t) (k : Fin n),
                                                                        Real.instLE.le (abs (alpha i j k))
                                                                          (HighamBench.gamma
                                                                            (HighamBench.p04EffectiveFmaRoundoff uBar
                                                                              uFma uOut)
                                                                            q)) →
                                                                      (∀ (i : Fin m) (j : Fin t) (k : Fin n),
                                                                          Real.instLE.le (abs (beta i j k))
                                                                            (HighamBench.gamma uBar n)) →
                                                                        HighamBench.P04MixedInputMatMulRun m n t b1 b b2
                                                                          p q r
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} →
  (row_dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) →
    (inner_dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
      (column_dimension_pos :
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t) →
        (row_block_size_pos :
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b1) →
          (inner_block_size_pos :
              @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b) →
            (column_block_size_pos :
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b2) →
              (row_block_count_pos :
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p) →
                (inner_block_count_pos :
                    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) →
                  (column_block_count_pos :
                      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r) →
                    (row_partition :
                        @Eq.{1} Nat m (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p b1)) →
                      (inner_partition :
                          @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
                        (column_partition :
                            @Eq.{1} Nat t (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r b2)) →
                          (A : Fin m → Fin n → Real) →
                            (B : Fin n → Fin t → Real) →
                              (convertedA : Fin m → Fin n → Real) →
                                (convertedB : Fin n → Fin t → Real) →
                                  (deltaA : Fin m → Fin n → Real) →
                                    (deltaB : Fin n → Fin t → Real) →
                                      (computed : Fin m → Fin t → Real) →
                                        (uLow uBar uFma uOut : Real) →
                                          (uLow_nonneg :
                                              @LE.le.{0} Real Real.instLE
                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                  (@Zero.toOfNat0.{0} Real Real.instZero))
                                                uLow) →
                                            (uBar_nonneg :
                                                @LE.le.{0} Real Real.instLE
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  uBar) →
                                              (uFma_nonneg :
                                                  @LE.le.{0} Real Real.instLE
                                                    (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                      (@Zero.toOfNat0.{0} Real Real.instZero))
                                                    uFma) →
                                                (uOut_nonneg :
                                                    @LE.le.{0} Real Real.instLE
                                                      (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                        (@Zero.toOfNat0.{0} Real Real.instZero))
                                                      uOut) →
                                                  (uBar_le_uFma : @LE.le.{0} Real Real.instLE uBar uFma) →
                                                    (effective_gamma_valid :
                                                        HighamBench.GammaValid
                                                          (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q) →
                                                      (internal_gamma_valid : HighamBench.GammaValid uBar n) →
                                                        (convertedA_eq :
                                                            ∀ (i : Fin m) (k : Fin n),
                                                              @Eq.{1} Real (convertedA i k)
                                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                  (@instHAdd.{0} Real Real.instAdd) (A i k)
                                                                  (deltaA i k))) →
                                                          (convertedB_eq :
                                                              ∀ (k : Fin n) (j : Fin t),
                                                                @Eq.{1} Real (convertedB k j)
                                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                    (@instHAdd.{0} Real Real.instAdd) (B k j)
                                                                    (deltaB k j))) →
                                                            (deltaA_bound :
                                                                ∀ (i : Fin m) (k : Fin n),
                                                                  @LE.le.{0} Real Real.instLE
                                                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                      (deltaA i k))
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul) uLow
                                                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                        (A i k)))) →
                                                              (deltaB_bound :
                                                                  ∀ (k : Fin n) (j : Fin t),
                                                                    @LE.le.{0} Real Real.instLE
                                                                      (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                        (deltaB k j))
                                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                        (@instHMul.{0} Real Real.instMul) uLow
                                                                        (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                          (B k j)))) →
                                                                (alpha beta : Fin m → Fin t → Fin n → Real) →
                                                                  (algorithm3_1_factorization :
                                                                      ∀ (i : Fin m) (j : Fin t),
                                                                        @Eq.{1} Real (computed i j)
                                                                          (@Finset.sum.{0, 0} (Fin n) Real
                                                                            Real.instAddCommMonoid
                                                                            (@Finset.univ.{0} (Fin n) (Fin.fintype n))
                                                                            fun (k : Fin n) =>
                                                                            @HMul.hMul.{0, 0, 0} Real Real Real
                                                                              (@instHMul.{0} Real Real.instMul)
                                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                (@instHMul.{0} Real Real.instMul)
                                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul)
                                                                                  (convertedA i k) (convertedB k j))
                                                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                                  (@instHAdd.{0} Real Real.instAdd)
                                                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                                    (@One.toOfNat1.{0} Real
                                                                                      Real.instOne))
                                                                                  (alpha i j k)))
                                                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                                (@instHAdd.{0} Real Real.instAdd)
                                                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                                                (beta i j k)))) →
                                                                    (alpha_bound :
                                                                        ∀ (i : Fin m) (j : Fin t) (k : Fin n),
                                                                          @LE.le.{0} Real Real.instLE
                                                                            (@abs.{0} Real Real.lattice
                                                                              Real.instAddGroup (alpha i j k))
                                                                            (HighamBench.gamma
                                                                              (HighamBench.p04EffectiveFmaRoundoff uBar
                                                                                uFma uOut)
                                                                              q)) →
                                                                      (beta_bound :
                                                                          ∀ (i : Fin m) (j : Fin t) (k : Fin n),
                                                                            @LE.le.{0} Real Real.instLE
                                                                              (@abs.{0} Real Real.lattice
                                                                                Real.instAddGroup (beta i j k))
                                                                              (HighamBench.gamma uBar n)) →
                                                                        HighamBench.P04MixedInputMatMulRun m n t b1 b b2
                                                                          p q r
```

### D014: `HighamBench.gamma`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D016: `Fin`

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

### D017: `HAdd.hAdd`

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

### D018: `HMul.hMul`

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

### D019: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D020: `HSub.hSub`

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

### D021: `LE.le`

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

### D022: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D023: `Nat`

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

### D024: `Nat.instAtLeastTwoHAddOfNat`

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

### D025: `Nat.instNeZeroSucc`

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

### D026: `OfNat.ofNat`

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

### D027: `One.toOfNat1`

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

### D028: `Real`

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

### D029: `Real.instAdd`

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

### D030: `Real.instAddGroup`

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

### D031: `Real.instLE`

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

### D032: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D033: `Real.instMul`

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

### D034: `Real.instNatCast`

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

### D035: `Real.instOne`

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

### D036: `Real.instSub`

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

### D037: `Real.lattice`

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

### D038: `abs`

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

### D039: `instHAdd`

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

### D040: `instHMul`

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

### D041: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D042: `instHSub`

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

### D043: `instOfNatAtLeastTwo`

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

### D044: `instOfNatNat`

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

### D045: `Fin.fintype`

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

### D046: `Finset.sum`

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

### D047: `Finset.univ`

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

### D048: `LT.lt`

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

### D049: `Real.decidableLE`

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

### D050: `Real.decidableLT`

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

### D051: `Real.instAddCommMonoid`

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

### D052: `Real.instLT`

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

### D053: `Real.instZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D054: `Zero.toOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D055: `ite`

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

### D056: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D057: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D058: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D059: `Nat.cast`

- Role: `external-frontier`
- Owner module: `Init.Data.Cast`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D060: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D061: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D062: `instLTNat`

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

### D063: `instMulNat`

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

### `HighamBench.P04Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P04Definitions.lean`
SHA-256: `d5ff5fe4b6ca28e0637b0df7bbc91a7f199b95caf4f4a32532ee14de9613f836`

```lean
import HighamBench.Core

namespace HighamBench

open scoped BigOperators

/-- The mixed-precision block-FMA coefficient occurring in P04 equations
(3.4)--(3.6). -/
noncomputable def p04BlockFmaCoeff
    (uFma u : ℝ) (q n : ℕ) : ℝ :=
  gamma uFma q + gamma u n + gamma uFma q * gamma u n

/-- The prioritized effective output-rounding parameter in P04 equation (3.3).
The first branch takes priority when the final output precision is coarser than
the block-FMA output precision. -/
noncomputable def p04EffectiveFmaRoundoff
    (uBar uFma uOut : ℝ) : ℝ :=
  if uFma < uOut then uOut
  else if uFma ≤ uBar then 0
  else uFma

/-- Exact finite dot product used in the scalar-entry analysis of Algorithm
3.1. -/
noncomputable def p04Dot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i * y i

/-- The componentwise data scale `|x|ᵀ|y|` in P04 equation (3.4). This is a
dot product of entrywise absolute values, not a norm. -/
noncomputable def p04AbsDot {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| * |y i|

/-- A scalar output of the chained block-FMA loop in Algorithm 3.1, represented
by the compact perturbation factorization immediately preceding equation
(3.4). The certificate is the paper's finite real standard-model semantics:
underflow, overflow, exceptional IEEE values, and the omitted second output
rounding are outside this model.

The unconditional `beta_bound` records the paper's statement that (3.4) is
valid for every evaluation order admitted by its analysis. `rightToLeft`
marks the blocked right-to-left case for which the paper supplies the sharper
`q+b-1` bound. -/
structure P04BlockFmaDotRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  x : Fin n → ℝ
  y : Fin n → ℝ
  computed : ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  algorithm3_1_factorization :
    computed = ∑ i : Fin n,
      x i * y i * (1 + alpha i) * (1 + beta i)
  alpha_bound : ∀ i,
    |alpha i| ≤ gamma (p04EffectiveFmaRoundoff uBar uFma uOut) q
  beta_bound : ∀ i, |beta i| ≤ gamma uBar n
  rightToLeft : Prop
  right_to_left_gamma_valid :
    rightToLeft → GammaValid uBar (q + b - 1)
  right_to_left_beta_bound :
    rightToLeft → ∀ i, |beta i| ≤ gamma uBar (q + b - 1)

/-- Rectangular matrix multiplication in the notation of P04 Theorem 3.2. -/
noncomputable def p04RectMatMul {m n t : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin t → ℝ) :
    Fin m → Fin t → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- The ordinary matrix product `|A||B|` in P04 equation (3.6), with absolute
values taken componentwise. This is not a matrix norm. -/
noncomputable def p04AbsRectMatMul {m n t : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin t → ℝ) :
    Fin m → Fin t → ℝ :=
  fun i j ↦ ∑ k : Fin n, |A i k| * |B k j|

/-- An execution of P04 Algorithm 3.1 for inputs not necessarily stored in the
low precision, represented by the standard-model certificates used to derive
Theorem 3.2. The `deltaA` and `deltaB` fields record line 1's componentwise
rounding errors. The indexed `alpha` and `beta` fields record the compact
factorization of every output entry derived from the chained block FMAs.

All values are finite reals. Thus this certificate has exactly the paper's
stated analysis scope: underflow, overflow, exceptional IEEE values, and the
second output rounding omitted in section 3.2 are outside the model. -/
structure P04MixedInputMatMulRun
    (m n t b1 b b2 p q r : ℕ) where
  row_dimension_pos : 0 < m
  inner_dimension_pos : 0 < n
  column_dimension_pos : 0 < t
  row_block_size_pos : 0 < b1
  inner_block_size_pos : 0 < b
  column_block_size_pos : 0 < b2
  row_block_count_pos : 0 < p
  inner_block_count_pos : 0 < q
  column_block_count_pos : 0 < r
  row_partition : m = p * b1
  inner_partition : n = q * b
  column_partition : t = r * b2
  A : Fin m → Fin n → ℝ
  B : Fin n → Fin t → ℝ
  convertedA : Fin m → Fin n → ℝ
  convertedB : Fin n → Fin t → ℝ
  deltaA : Fin m → Fin n → ℝ
  deltaB : Fin n → Fin t → ℝ
  computed : Fin m → Fin t → ℝ
  uLow : ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uLow_nonneg : 0 ≤ uLow
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  convertedA_eq : ∀ i k, convertedA i k = A i k + deltaA i k
  convertedB_eq : ∀ k j, convertedB k j = B k j + deltaB k j
  deltaA_bound : ∀ i k, |deltaA i k| ≤ uLow * |A i k|
  deltaB_bound : ∀ k j, |deltaB k j| ≤ uLow * |B k j|
  alpha : Fin m → Fin t → Fin n → ℝ
  beta : Fin m → Fin t → Fin n → ℝ
  algorithm3_1_factorization : ∀ i j,
    computed i j = ∑ k : Fin n,
      convertedA i k * convertedB k j *
        (1 + alpha i j k) * (1 + beta i j k)
  alpha_bound : ∀ i j k,
    |alpha i j k| ≤
      gamma (p04EffectiveFmaRoundoff uBar uFma uOut) q
  beta_bound : ∀ i j k, |beta i j k| ≤ gamma uBar n

/-- The factorization-stage coefficient in P04 equations (4.4) and (4.7). -/
noncomputable def p04FactorizationCoeff
    (uLow uBar uFma uWork : ℝ) (q n b : ℕ) : ℝ :=
  2 * uLow + uLow ^ 2 +
    max
      (p04BlockFmaCoeff
        (p04EffectiveFmaRoundoff uBar uFma uWork)
        uBar (q - 1) (n - b + 1))
      (gamma uWork b) * (1 + uLow) ^ 2

/-- Square matrix multiplication in the paper's finite-index notation. -/
noncomputable def p04MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Matrix-vector multiplication in the paper's finite-index notation. -/
noncomputable def p04MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, A i j * x j

/-- The componentwise absolute product `|L||U|` in P04 equations (4.4) and
(4.7). -/
noncomputable def p04AbsMatMul {n : ℕ}
    (L U : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ k : Fin n, |L i k| * |U k j|

/-- The mandatory componentwise scale `|A| + |Lhat||Uhat|` in P04 equations
(4.4) and (4.7). -/
noncomputable def p04LUSolveScale {n : ℕ}
    (A LHat UHat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => |A i j| + p04AbsMatMul LHat UHat i j

/-- Entrywise lower-triangularity for the computed factor in Algorithm 4.1. -/
def p04IsLowerTriangular {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, i.val < j.val → L i j = 0

/-- Entrywise upper-triangularity for the computed factor in Algorithm 4.1. -/
def p04IsUpperTriangular {n : ℕ} (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → U i j = 0

/-- A complete finite-real execution certificate for P04 Algorithm 4.1 followed
by forward and backward substitution, as used in Theorem 4.4. The factorization
fields record Theorem 4.3's consequence for the computed factors; the solve
fields record the standard triangular-substitution backward errors invoked in
the proof of Theorem 4.4. The final perturbation from equation (4.7) is not a
field and must be constructed by the target theorem.

The certificate represents successful execution in the paper's standard model.
Underflow, overflow, exceptional IEEE values, and the double-rounding effect
omitted by the paper are outside this finite-real model. -/
structure P04BlockLUSolveRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  A : Fin n → Fin n → ℝ
  LHat : Fin n → Fin n → ℝ
  UHat : Fin n → Fin n → ℝ
  lower_triangular : p04IsLowerTriangular LHat
  upper_triangular : p04IsUpperTriangular UHat
  lower_unit_diagonal : ∀ i, LHat i i = 1
  upper_diagonal_nonzero : ∀ i, UHat i i ≠ 0
  uLow : ℝ
  uBar : ℝ
  uFma : ℝ
  uWork : ℝ
  uLow_nonneg : 0 ≤ uLow
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uWork_nonneg : 0 ≤ uWork
  uBar_le_uFma : uBar ≤ uFma
  effective_factor_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uWork) (q - 1)
  internal_factor_gamma_valid : GammaValid uBar (n - b + 1)
  working_block_gamma_valid : GammaValid uWork b
  working_solve_gamma_valid : GammaValid uWork n
  factorError : Fin n → Fin n → ℝ
  algorithm4_1_factorization : p04MatMul LHat UHat = A + factorError
  factor_error_bound : ∀ i j,
    |factorError i j| ≤
      p04FactorizationCoeff uLow uBar uFma uWork q n b *
        p04LUSolveScale A LHat UHat i j
  xHat : Fin n → ℝ
  yHat : Fin n → ℝ
  rhs : Fin n → ℝ
  deltaL : Fin n → Fin n → ℝ
  deltaU : Fin n → Fin n → ℝ
  forward_substitution : p04MatVec (LHat + deltaL) yHat = rhs
  backward_substitution : p04MatVec (UHat + deltaU) xHat = yHat
  deltaL_bound : ∀ i j,
    |deltaL i j| ≤ gamma uWork n * |LHat i j|
  deltaU_bound : ∀ i j,
    |deltaU i j| ≤ gamma uWork n * |UHat i j|

end HighamBench
```
