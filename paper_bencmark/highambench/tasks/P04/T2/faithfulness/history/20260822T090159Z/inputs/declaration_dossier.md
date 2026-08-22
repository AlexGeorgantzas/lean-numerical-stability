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
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `c3657a172774a894e09903a41ae9c64cfbe859d131089602987cf4154206e64f`

Type:

```lean
{m n t b1 b b2 p q r : Nat} → HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Fin m → Fin t → Real
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} → (run : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Fin m → Fin t → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m n t b1 b b2 p q r} run i j => (run.entryRun i j).computed
```

### D005: `HighamBench.P04MixedInputMatMulRun.uBar`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `3e6c034dd41a19f356130cb7c9a857813728280e50136c35305dbc048ace962d`

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
fun m n t b1 b b2 p q r self => self.19
```

### D006: `HighamBench.P04MixedInputMatMulRun.uFma`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `20b009beccf147fcb45d8ba829bc4a4a7e671400392db0361ab222f61bf75375`

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

### D007: `HighamBench.P04MixedInputMatMulRun.uLow`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8d6b65c8435748129fc13161c7fb6a47357ea95f36508bba87fffa473c3ce35b`

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
fun m n t b1 b b2 p q r self => self.17
```

### D008: `HighamBench.P04MixedInputMatMulRun.uOut`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8d5bef9a4f8397036f10b208f4ad9290432f87bbd7e18ed26630a1c77416fccc`

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

### D013: `HighamBench.P04BlockFmaDotRun.computed`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c3eb4eadcd87bb71cef99dd87735ab5c04942df5d1f8df1fc1986c9b6389202a`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (run : HighamBench.P04BlockFmaDotRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n b q} run => run.state q
```

### D014: `HighamBench.P04MixedInputMatMulRun.entryRun`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `e3f67e94ce22efc482e70a3491aed593988ab5bce6f78337344a03693388344b`

Type:

```lean
{m n t b1 b b2 p q r : Nat} →
  HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r → Fin m → Fin t → HighamBench.P04BlockFmaDotRun n b q
```

Fully explicit type:

```lean
{m n t b1 b b2 p q r : Nat} →
  (self : HighamBench.P04MixedInputMatMulRun m n t b1 b b2 p q r) → Fin m → Fin t → HighamBench.P04BlockFmaDotRun n b q
```

Definition body (one-level semantic boundary):

```lean
fun m n t b1 b b2 p q r self => self.35
```

### D015: `HighamBench.P04MixedInputMatMulRun.mk`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `96d1ee30b890784a4f00c3d775cb6cda1dca422fb331907aedb60a7a6b5f39d5`

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
                      (inner_partition : Eq n (instHMul.hMul q b)) →
                        Eq t (instHMul.hMul r b2) →
                          (A : Fin m → Fin n → Real) →
                            (B : Fin n → Fin t → Real) →
                              (inputErrorA : Fin m → Fin n → Real) →
                                (inputErrorB : Fin n → Fin t → Real) →
                                  (uLow uHigh uBar uFma uOut : Real) →
                                    Real.instLE.le 0 uLow →
                                      Real.instLE.le 0 uHigh →
                                        Real.instLE.le 0 uBar →
                                          Real.instLE.le 0 uFma →
                                            Real.instLE.le 0 uOut →
                                              Real.instLE.le uHigh uLow →
                                                Or (Eq uFma uLow) (Eq uFma uHigh) →
                                                  Or (Eq uOut uLow) (Eq uOut uHigh) →
                                                    Real.instLE.le uBar uFma →
                                                      HighamBench.GammaValid
                                                          (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q →
                                                        HighamBench.GammaValid uBar n →
                                                          (∀ (i : Fin m) (k : Fin n),
                                                              Real.instLE.le (abs (inputErrorA i k)) uLow) →
                                                            (∀ (k : Fin n) (j : Fin t),
                                                                Real.instLE.le (abs (inputErrorB k j)) uLow) →
                                                              (entryRun :
                                                                  Fin m → Fin t → HighamBench.P04BlockFmaDotRun n b q) →
                                                                (∀ (i : Fin m) (j : Fin t),
                                                                    Eq (entryRun i j).uBar uBar) →
                                                                  (∀ (i : Fin m) (j : Fin t),
                                                                      Eq (entryRun i j).uFma uFma) →
                                                                    (∀ (i : Fin m) (j : Fin t),
                                                                        Eq (entryRun i j).uOut uOut) →
                                                                      (∀ (i : Fin m) (j : Fin t) (k : Fin q)
                                                                          (l : Fin b),
                                                                          Eq ((entryRun i j).x k l)
                                                                            (instHMul.hMul
                                                                              (A i
                                                                                (HighamBench.p04BlockIndex
                                                                                  inner_partition k l))
                                                                              (instHAdd.hAdd 1
                                                                                (inputErrorA i
                                                                                  (HighamBench.p04BlockIndex
                                                                                    inner_partition k l))))) →
                                                                        (∀ (i : Fin m) (j : Fin t) (k : Fin q)
                                                                            (l : Fin b),
                                                                            Eq ((entryRun i j).y k l)
                                                                              (instHMul.hMul
                                                                                (B
                                                                                  (HighamBench.p04BlockIndex
                                                                                    inner_partition k l)
                                                                                  j)
                                                                                (instHAdd.hAdd 1
                                                                                  (inputErrorB
                                                                                    (HighamBench.p04BlockIndex
                                                                                      inner_partition k l)
                                                                                    j)))) →
                                                                          HighamBench.P04MixedInputMatMulRun m n t b1 b
                                                                            b2 p q r
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
                              (inputErrorA : Fin m → Fin n → Real) →
                                (inputErrorB : Fin n → Fin t → Real) →
                                  (uLow uHigh uBar uFma uOut : Real) →
                                    (uLow_nonneg :
                                        @LE.le.{0} Real Real.instLE
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                          uLow) →
                                      (uHigh_nonneg :
                                          @LE.le.{0} Real Real.instLE
                                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                            uHigh) →
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
                                              (uHigh_le_uLow : @LE.le.{0} Real Real.instLE uHigh uLow) →
                                                (uFma_allowed : Or (@Eq.{1} Real uFma uLow) (@Eq.{1} Real uFma uHigh)) →
                                                  (uOut_allowed :
                                                      Or (@Eq.{1} Real uOut uLow) (@Eq.{1} Real uOut uHigh)) →
                                                    (uBar_le_uFma : @LE.le.{0} Real Real.instLE uBar uFma) →
                                                      (effective_gamma_valid :
                                                          HighamBench.GammaValid
                                                            (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q) →
                                                        (internal_gamma_valid : HighamBench.GammaValid uBar n) →
                                                          (input_error_A_bound :
                                                              ∀ (i : Fin m) (k : Fin n),
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    (inputErrorA i k))
                                                                  uLow) →
                                                            (input_error_B_bound :
                                                                ∀ (k : Fin n) (j : Fin t),
                                                                  @LE.le.{0} Real Real.instLE
                                                                    (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                      (inputErrorB k j))
                                                                    uLow) →
                                                              (entryRun :
                                                                  Fin m → Fin t → HighamBench.P04BlockFmaDotRun n b q) →
                                                                (entry_run_uBar :
                                                                    ∀ (i : Fin m) (j : Fin t),
                                                                      @Eq.{1} Real
                                                                        (@HighamBench.P04BlockFmaDotRun.uBar n b q
                                                                          (entryRun i j))
                                                                        uBar) →
                                                                  (entry_run_uFma :
                                                                      ∀ (i : Fin m) (j : Fin t),
                                                                        @Eq.{1} Real
                                                                          (@HighamBench.P04BlockFmaDotRun.uFma n b q
                                                                            (entryRun i j))
                                                                          uFma) →
                                                                    (entry_run_uOut :
                                                                        ∀ (i : Fin m) (j : Fin t),
                                                                          @Eq.{1} Real
                                                                            (@HighamBench.P04BlockFmaDotRun.uOut n b q
                                                                              (entryRun i j))
                                                                            uOut) →
                                                                      (entry_run_x :
                                                                          ∀ (i : Fin m) (j : Fin t) (k : Fin q)
                                                                            (l : Fin b),
                                                                            @Eq.{1} Real
                                                                              (@HighamBench.P04BlockFmaDotRun.x n b q
                                                                                (entryRun i j) k l)
                                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                (@instHMul.{0} Real Real.instMul)
                                                                                (A i
                                                                                  (@HighamBench.p04BlockIndex n q b
                                                                                    inner_partition k l))
                                                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                                  (@instHAdd.{0} Real Real.instAdd)
                                                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                                    (@One.toOfNat1.{0} Real
                                                                                      Real.instOne))
                                                                                  (inputErrorA i
                                                                                    (@HighamBench.p04BlockIndex n q b
                                                                                      inner_partition k l))))) →
                                                                        (entry_run_y :
                                                                            ∀ (i : Fin m) (j : Fin t) (k : Fin q)
                                                                              (l : Fin b),
                                                                              @Eq.{1} Real
                                                                                (@HighamBench.P04BlockFmaDotRun.y n b q
                                                                                  (entryRun i j) k l)
                                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                                  (@instHMul.{0} Real Real.instMul)
                                                                                  (B
                                                                                    (@HighamBench.p04BlockIndex n q b
                                                                                      inner_partition k l)
                                                                                    j)
                                                                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                                    (@instHAdd.{0} Real Real.instAdd)
                                                                                    (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                                      (@One.toOfNat1.{0} Real
                                                                                        Real.instOne))
                                                                                    (inputErrorB
                                                                                      (@HighamBench.p04BlockIndex n q b
                                                                                        inner_partition k l)
                                                                                      j)))) →
                                                                          HighamBench.P04MixedInputMatMulRun m n t b1 b
                                                                            b2 p q r
```

### D016: `HighamBench.gamma`

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

### D017: `HighamBench.GammaValid`

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

### D018: `HighamBench.P04BlockFmaDotRun`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `4944bca2329eb454982d0814cc41eeb43369f287267aa02482bb780f17148ce2`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(n b q : Nat) → Type
```

### D019: `HighamBench.P04BlockFmaDotRun.state`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `afc5091f30061a4695e670afab99786fa31bd80e06e01494c40cad4fb27919d3`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Nat → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.17
```

### D020: `HighamBench.P04BlockFmaDotRun.uBar`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `41c0a0cc6168be2bf81c18f69b9a68ec790f9ba792c6f8c204b8f50beaeec4d9`

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

### D021: `HighamBench.P04BlockFmaDotRun.uFma`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `e2b22ca607ce748685985331ec008998a2298f54ce905af81eb6772c009c7e4f`

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

### D022: `HighamBench.P04BlockFmaDotRun.uOut`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `104f8dfbddf61964ceffaec223529dd8fcf200618b860378165a154b0c99ea9a`

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

### D023: `HighamBench.P04BlockFmaDotRun.x`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `17490b7d9bdf5e3cca3cf8c15a8c60dbd6d3844f4b899ceab499c95e9c9d6803`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Fin q → Fin b → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Fin q → Fin b → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.5
```

### D024: `HighamBench.P04BlockFmaDotRun.y`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d89893ea364358e94343a07e992bc287bc49546cbcb351875c7f77ad22c0fb6f`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockFmaDotRun n b q → Fin q → Fin b → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockFmaDotRun n b q) → Fin q → Fin b → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.6
```

### D025: `HighamBench.p04BlockIndex`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `86723a91477d3543e9ea2051e883f991f2d176c847273eb5b2f7ac7e0a48f562`

Type:

```lean
{n q b : Nat} → Eq n (instHMul.hMul q b) → Fin q → Fin b → Fin n
```

Fully explicit type:

```lean
{n q b : Nat} →
  (h : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
    (k : Fin q) → (j : Fin b) → Fin n
```

Definition body (one-level semantic boundary):

```lean
fun {n q b} h k j => EquivLike.toFunLike.coe (HighamBench.p04BlockIndexEquiv h) { fst := k, snd := j }
```

### D026: `HighamBench.P04BlockFmaDotRun.mk`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `7627fc4e7244dcfdc166578032417ad1eb8ec07c078174c3fa7427b335142b0c`

Type:

```lean
{n b q : Nat} →
  instLTNat.lt 0 n →
    instLTNat.lt 0 b →
      instLTNat.lt 0 q →
        Eq n (instHMul.hMul q b) →
          (x y : Fin q → Fin b → Real) →
            (uBar uFma uOut : Real) →
              Real.instLE.le 0 uBar →
                Real.instLE.le 0 uFma →
                  Real.instLE.le 0 uOut →
                    Real.instLE.le uBar uFma →
                      HighamBench.GammaValid (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut) q →
                        HighamBench.GammaValid uBar n →
                          (order : HighamBench.P04BlockEvaluationOrder) →
                            (state : Nat → Real) →
                              (carryTheta : Fin q → Real) →
                                (termTheta : Fin q → Fin b → Real) →
                                  (delta : Fin q → Real) →
                                    Eq (state 0) 0 →
                                      (∀ (k : Fin q),
                                          Eq (state (instHAdd.hAdd k.val 1))
                                            (instHMul.hMul
                                              (instHAdd.hAdd
                                                (instHMul.hMul (state k.val) (instHAdd.hAdd 1 (carryTheta k)))
                                                (Finset.univ.sum fun j =>
                                                  instHMul.hMul (instHMul.hMul (x k j) (y k j))
                                                    (instHAdd.hAdd 1 (termTheta k j))))
                                              (instHAdd.hAdd 1 (delta k)))) →
                                        (∀ (k : Fin q),
                                            Real.instLE.le (abs (delta k))
                                              (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut)) →
                                          (∀ (k : Fin q),
                                              Real.instLE.le (abs (carryTheta k)) (HighamBench.gamma uBar b)) →
                                            (∀ (k : Fin q) (j : Fin b),
                                                Real.instLE.le (abs (termTheta k j))
                                                  (HighamBench.gamma uBar (ite (Eq k.val 0) b (instHAdd.hAdd b 1)))) →
                                              (Eq order HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                  ∀ (k : Fin q),
                                                    Real.instLE.le (abs (carryTheta k)) (HighamBench.gamma uBar 1)) →
                                                (innerPathError : Fin q → Fin b → Fin n → Real) →
                                                  (∀ (k : Fin q) (j : Fin b) (r : Fin n),
                                                      Real.instLE.le (abs (innerPathError k j r)) uBar) →
                                                    (∀ (k : Fin q) (j : Fin b),
                                                        Eq
                                                          (Finset.univ.prod fun r =>
                                                            instHAdd.hAdd 1 (innerPathError k j r))
                                                          (instHMul.hMul (instHAdd.hAdd 1 (termTheta k j))
                                                            (HighamBench.p04StrictErrorProduct carryTheta k))) →
                                                      (rightToLeftPathError :
                                                          Fin q →
                                                            Fin b → Fin (instHSub.hSub (instHAdd.hAdd q b) 1) → Real) →
                                                        (Eq order HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                            ∀ (k : Fin q) (j : Fin b)
                                                              (r : Fin (instHSub.hSub (instHAdd.hAdd q b) 1)),
                                                              Real.instLE.le (abs (rightToLeftPathError k j r)) uBar) →
                                                          (Eq order HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                              ∀ (k : Fin q) (j : Fin b),
                                                                Eq
                                                                  (Finset.univ.prod fun r =>
                                                                    instHAdd.hAdd 1 (rightToLeftPathError k j r))
                                                                  (instHMul.hMul (instHAdd.hAdd 1 (termTheta k j))
                                                                    (HighamBench.p04StrictErrorProduct carryTheta k))) →
                                                            HighamBench.P04BlockFmaDotRun n b q
```

Fully explicit type:

```lean
{n b q : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (block_size_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b) →
      (block_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) →
        (dimension_eq : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
          (x y : Fin q → Fin b → Real) →
            (uBar uFma uOut : Real) →
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
                          (order : HighamBench.P04BlockEvaluationOrder) →
                            (state : Nat → Real) →
                              (carryTheta : Fin q → Real) →
                                (termTheta : Fin q → Fin b → Real) →
                                  (delta : Fin q → Real) →
                                    (state_zero :
                                        @Eq.{1} Real
                                          (state (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                                      (state_step :
                                          ∀ (k : Fin q),
                                            @Eq.{1} Real
                                              (state
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@Fin.val q k)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (state (@Fin.val q k))
                                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                      (@instHAdd.{0} Real Real.instAdd)
                                                      (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                        (@One.toOfNat1.{0} Real Real.instOne))
                                                      (carryTheta k)))
                                                  (@Finset.sum.{0, 0} (Fin b) Real Real.instAddCommMonoid
                                                    (@Finset.univ.{0} (Fin b) (Fin.fintype b)) fun (j : Fin b) =>
                                                    @HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul) (x k j) (y k j))
                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                        (@instHAdd.{0} Real Real.instAdd)
                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                          (@One.toOfNat1.{0} Real Real.instOne))
                                                        (termTheta k j))))
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                    (@One.toOfNat1.{0} Real Real.instOne))
                                                  (delta k)))) →
                                        (delta_bound :
                                            ∀ (k : Fin q),
                                              @LE.le.{0} Real Real.instLE
                                                (@abs.{0} Real Real.lattice Real.instAddGroup (delta k))
                                                (HighamBench.p04EffectiveFmaRoundoff uBar uFma uOut)) →
                                          (carry_theta_bound :
                                              ∀ (k : Fin q),
                                                @LE.le.{0} Real Real.instLE
                                                  (@abs.{0} Real Real.lattice Real.instAddGroup (carryTheta k))
                                                  (HighamBench.gamma uBar b)) →
                                            (term_theta_bound :
                                                ∀ (k : Fin q) (j : Fin b),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@abs.{0} Real Real.lattice Real.instAddGroup (termTheta k j))
                                                    (HighamBench.gamma uBar
                                                      (@ite.{1} Nat
                                                        (@Eq.{1} Nat (@Fin.val q k)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (instDecidableEqNat (@Fin.val q k)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        b
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          b
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))) →
                                              (right_to_left_carry_bound :
                                                  @Eq.{1} HighamBench.P04BlockEvaluationOrder order
                                                      HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                    ∀ (k : Fin q),
                                                      @LE.le.{0} Real Real.instLE
                                                        (@abs.{0} Real Real.lattice Real.instAddGroup (carryTheta k))
                                                        (HighamBench.gamma uBar
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) →
                                                (innerPathError : Fin q → Fin b → Fin n → Real) →
                                                  (inner_path_error_bound :
                                                      ∀ (k : Fin q) (j : Fin b) (r : Fin n),
                                                        @LE.le.{0} Real Real.instLE
                                                          (@abs.{0} Real Real.lattice Real.instAddGroup
                                                            (innerPathError k j r))
                                                          uBar) →
                                                    (inner_path_factor :
                                                        ∀ (k : Fin q) (j : Fin b),
                                                          @Eq.{1} Real
                                                            (@Finset.prod.{0, 0} (Fin n) Real Real.instCommMonoid
                                                              (@Finset.univ.{0} (Fin n) (Fin.fintype n))
                                                              fun (r : Fin n) =>
                                                              @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                (@instHAdd.{0} Real Real.instAdd)
                                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                                (innerPathError k j r))
                                                            (@HMul.hMul.{0, 0, 0} Real Real Real
                                                              (@instHMul.{0} Real Real.instMul)
                                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                (@instHAdd.{0} Real Real.instAdd)
                                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                  (@One.toOfNat1.{0} Real Real.instOne))
                                                                (termTheta k j))
                                                              (@HighamBench.p04StrictErrorProduct q carryTheta k))) →
                                                      (rightToLeftPathError :
                                                          Fin q →
                                                            Fin b →
                                                              Fin
                                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                    (@instHSub.{0} Nat instSubNat)
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) q b)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1)))) →
                                                                Real) →
                                                        (right_to_left_path_error_bound :
                                                            @Eq.{1} HighamBench.P04BlockEvaluationOrder order
                                                                HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                              ∀ (k : Fin q) (j : Fin b)
                                                                (r :
                                                                  Fin
                                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                      (@instHSub.{0} Nat instSubNat)
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) q b)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))),
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    (rightToLeftPathError k j r))
                                                                  uBar) →
                                                          (right_to_left_path_factor :
                                                              @Eq.{1} HighamBench.P04BlockEvaluationOrder order
                                                                  HighamBench.P04BlockEvaluationOrder.rightToLeft →
                                                                ∀ (k : Fin q) (j : Fin b),
                                                                  @Eq.{1} Real
                                                                    (@Finset.prod.{0, 0}
                                                                      (Fin
                                                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                          (@instHSub.{0} Nat instSubNat)
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) q b)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1)))))
                                                                      Real Real.instCommMonoid
                                                                      (@Finset.univ.{0}
                                                                        (Fin
                                                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                            (@instHSub.{0} Nat instSubNat)
                                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                              (@instHAdd.{0} Nat instAddNat) q b)
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                              (instOfNatNat (nat_lit 1)))))
                                                                        (Fin.fintype
                                                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                            (@instHSub.{0} Nat instSubNat)
                                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                              (@instHAdd.{0} Nat instAddNat) q b)
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                              (instOfNatNat (nat_lit 1))))))
                                                                      fun
                                                                        (r :
                                                                          Fin
                                                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                              (@instHSub.{0} Nat instSubNat)
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat) q b)
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                (instOfNatNat (nat_lit 1))))) =>
                                                                      @HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                        (@instHAdd.{0} Real Real.instAdd)
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                          (@One.toOfNat1.{0} Real Real.instOne))
                                                                        (rightToLeftPathError k j r))
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul)
                                                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                        (@instHAdd.{0} Real Real.instAdd)
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                          (@One.toOfNat1.{0} Real Real.instOne))
                                                                        (termTheta k j))
                                                                      (@HighamBench.p04StrictErrorProduct q carryTheta
                                                                        k))) →
                                                            HighamBench.P04BlockFmaDotRun n b q
```

### D027: `HighamBench.p04BlockIndexEquiv`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `e57ba10d009c3cc57982a6be035df777df359b1b2f2e25f86d7e1b23aae4ce79`

Type:

```lean
{n q b : Nat} → Eq n (instHMul.hMul q b) → Equiv (Prod (Fin q) (Fin b)) (Fin n)
```

Fully explicit type:

```lean
{n q b : Nat} →
  (h : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
    Equiv.{1, 1} (Prod.{0, 0} (Fin q) (Fin b)) (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n q b} h => finProdFinEquiv.trans (finCongr ⋯)
```

### D028: `HighamBench.P04BlockEvaluationOrder`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `58340acc7504455e3288212d0336b5c0d7ab3feafd953ac30df0858c48709e5e`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D029: `HighamBench.P04BlockEvaluationOrder.rightToLeft`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `7f4e5396a430e3e0762dddd0e56e4a05427324b97c006713ec9424b1ff151084`

Type:

```lean
HighamBench.P04BlockEvaluationOrder
```

Fully explicit type:

```lean
HighamBench.P04BlockEvaluationOrder
```

### D030: `HighamBench.p04BlockIndexEquiv._proof_1`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `theorem`
- Distance from target type: `5`
- Semantic SHA-256: `7c9084cf6d89849970c15ee23c81d7f3d8e55d9427bff543135f75d4a09f8a24`

Type:

```lean
∀ {n q b : Nat}, Eq n (instHMul.hMul q b) → Eq (instHMul.hMul q b) n
```

Fully explicit type:

```lean
∀ {n q b : Nat} (h : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)),
  @Eq.{1} Nat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b) n
```

### D031: `HighamBench.p04StrictErrorProduct`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `dcc4e809ac9b8a385e972a2966fd2e478c43899de1595c5932678f2adea7911c`

Type:

```lean
{q : Nat} → (Fin q → Real) → Fin q → Real
```

Fully explicit type:

```lean
{q : Nat} → (error : Fin q → Real) → (k : Fin q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {q} error k => (Finset.Ico (instHAdd.hAdd k.val 1) q).prod fun l => instHAdd.hAdd 1 (HighamBench.p04ErrorAt error l)
```

### D032: `HighamBench.P04BlockEvaluationOrder.leftToRight`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `238cca16f93bd483f05f4b1dba71d774f3803a2b5fc727ccb3539659c5f4dd52`

Type:

```lean
HighamBench.P04BlockEvaluationOrder
```

Fully explicit type:

```lean
HighamBench.P04BlockEvaluationOrder
```

### D033: `HighamBench.P04BlockEvaluationOrder.other`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `26ef234a89eb1ba00d8d4f2c5d456da095913ca53729633625ffa4bc91c65d1e`

Type:

```lean
Nat → HighamBench.P04BlockEvaluationOrder
```

Fully explicit type:

```lean
(code : Nat) → HighamBench.P04BlockEvaluationOrder
```

### D034: `HighamBench.p04ErrorAt`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `719296617c1e16a2c6fbcc5bbf40acf7abbb9f43c60231fc3e43cf8151e467d3`

Type:

```lean
{q : Nat} → (Fin q → Real) → Nat → Real
```

Fully explicit type:

```lean
{q : Nat} → (error : Fin q → Real) → (k : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {q} error k => if h : instLTNat.lt k q then error ⟨k, h⟩ else 0
```

### D035: `Fin`

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

### D036: `HAdd.hAdd`

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

### D037: `HMul.hMul`

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

### D038: `HPow.hPow`

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

### D039: `HSub.hSub`

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

### D040: `LE.le`

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

### D041: `Monoid.toNatPow`

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

### D042: `Nat`

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

### D043: `Nat.instAtLeastTwoHAddOfNat`

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

### D044: `Nat.instNeZeroSucc`

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

### D045: `OfNat.ofNat`

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

### D046: `One.toOfNat1`

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

### D047: `Real`

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

### D048: `Real.instAdd`

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

### D049: `Real.instAddGroup`

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

### D050: `Real.instLE`

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

### D051: `Real.instMonoid`

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

### D052: `Real.instMul`

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

### D053: `Real.instNatCast`

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

### D054: `Real.instOne`

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

### D055: `Real.instSub`

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

### D056: `Real.lattice`

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

### D057: `abs`

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

### D058: `instHAdd`

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

### D059: `instHMul`

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

### D060: `instHPow`

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

### D061: `instHSub`

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

### D062: `instOfNatAtLeastTwo`

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

### D063: `instOfNatNat`

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

### D064: `Fin.fintype`

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

### D065: `Finset.sum`

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

### D066: `Finset.univ`

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

### D067: `LT.lt`

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

### D068: `Real.decidableLE`

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

### D069: `Real.decidableLT`

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

### D070: `Real.instAddCommMonoid`

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

### D071: `Real.instLT`

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

### D072: `Real.instZero`

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

### D073: `Zero.toOfNat0`

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

### D074: `ite`

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

### D075: `DivInvMonoid.toDiv`

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

### D076: `Eq`

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

### D077: `HDiv.hDiv`

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

### D078: `Nat.cast`

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

### D079: `Or`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `de438fb54053199506d3db7df89e4ed6f1bc296d2e49a7e63e7a4b73a1b23d7e`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D080: `Real.instDivInvMonoid`

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

### D081: `instHDiv`

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

### D082: `instLTNat`

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

### D083: `instMulNat`

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

### D084: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D085: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

Fully explicit type:

```lean
(α : Sort u_1) → (β : Sort u_2) → Sort (max (max 1 u_1) u_2)
```

### D086: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D087: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D088: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D089: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (fst : α) → (snd : β) → Prod.{u, v} α β
```

### D090: `Equiv.trans`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f384b3f3d2cdbfe07f1bc263de5981a9b809b2a233ea1ca41e24c49fb6084310`

Type:

```lean
{α : Sort u} → {β : Sort v} → {γ : Sort w} → Equiv α β → Equiv β γ → Equiv α γ
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → {γ : Sort w} → (e₁ : Equiv.{u, v} α β) → (e₂ : Equiv.{v, w} β γ) → Equiv.{u, w} α γ
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} {γ} e₁ e₂ =>
  { toFun := Function.comp (EquivLike.toFunLike.coe e₂) (EquivLike.toFunLike.coe e₁),
    invFun := Function.comp (EquivLike.toFunLike.coe e₁.symm) (EquivLike.toFunLike.coe e₂.symm), left_inv := ⋯,
    right_inv := ⋯ }
```

### D091: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D092: `Finset.prod`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `e364cffe1f2457eedceca9fe0617d7a66084963ffb6e6ed760d1f3fe74eee841`

Type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid M] → Finset ι → (ι → M) → M
```

Fully explicit type:

```lean
{ι : Type u_1} → {M : Type u_3} → [CommMonoid.{u_3} M] → (s : Finset.{u_1} ι) → (f : ι → M) → M
```

Definition body (one-level semantic boundary):

```lean
fun {ι} {M} [CommMonoid M] s f => (Multiset.map f s.val).prod
```

### D093: `Real.instCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f537dc5e9be2b886066e25d0f560dc52fd1be771759ec3e7b40a5f5f3e6c6467`

Type:

```lean
CommMonoid Real
```

Fully explicit type:

```lean
CommMonoid.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D094: `finCongr`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fin.SuccPred`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `0382b16a04b223d3f1e208b79831014456e167607827dd36b7d5720383b6c20e`

Type:

```lean
{n m : Nat} → Eq n m → Equiv (Fin n) (Fin m)
```

Fully explicit type:

```lean
{n m : Nat} → (eq : @Eq.{1} Nat n m) → Equiv.{1, 1} (Fin n) (Fin m)
```

Definition body (one-level semantic boundary):

```lean
fun {n m} eq => { toFun := Fin.cast eq, invFun := Fin.cast ⋯, left_inv := ⋯, right_inv := ⋯ }
```

### D095: `finProdFinEquiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `c424cb745692eb8ba1a5fb3d5530ab0685d9d2adbd10531993bdc471f890a58f`

Type:

```lean
{m n : Nat} → Equiv (Prod (Fin m) (Fin n)) (Fin (instHMul.hMul m n))
```

Fully explicit type:

```lean
{m n : Nat} →
  Equiv.{1, 1} (Prod.{0, 0} (Fin m) (Fin n)) (Fin (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m n))
```

Definition body (one-level semantic boundary):

```lean
fun {m n} =>
  { toFun := fun x => ⟨instHAdd.hAdd x.snd.val (instHMul.hMul n x.fst.val), ⋯⟩,
    invFun := fun x => { fst := x.divNat, snd := x.modNat }, left_inv := ⋯, right_inv := ⋯ }
```

### D096: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D097: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `658bdfe7785c44f21a851cae8ec44aec53d69bb69af955a9d42028df3fe37d22`

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

### D098: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D099: `Finset.Ico`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Interval.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `256e28d69fc14d1c084345d68cbe49ed3d7c9201ffebf16a70893f13dcafaf29`

Type:

```lean
{α : Type u_1} → [inst : Preorder α] → [LocallyFiniteOrder α] → α → α → Finset α
```

Fully explicit type:

```lean
{α : Type u_1} → [inst : Preorder.{u_1} α] → [@LocallyFiniteOrder.{u_1} α inst] → (a b : α) → Finset.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [Preorder α] [inst_1 : LocallyFiniteOrder α] a b => inst_1.finsetIco a b
```

### D100: `Nat.instLocallyFiniteOrder`

- Role: `external-frontier`
- Owner module: `Mathlib.Order.Interval.Finset.Nat`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `8161a27efe4a0d75ef79e9a0fb2477c8f9f3df6dbf2ddc8cd26e705d3d59a945`

Type:

```lean
LocallyFiniteOrder Nat
```

Fully explicit type:

```lean
@LocallyFiniteOrder.{0} Nat Nat.instPreorder
```

Definition body (one-level semantic boundary):

```lean
{ finsetIcc := fun a b => { val := Multiset.ofList (List.range' a (instHSub.hSub (instHAdd.hAdd b 1) a)), nodup := ⋯ },
  finsetIco := fun a b => { val := Multiset.ofList (List.range' a (instHSub.hSub b a)), nodup := ⋯ },
  finsetIoc := fun a b => { val := Multiset.ofList (List.range' (instHAdd.hAdd a 1) (instHSub.hSub b a)), nodup := ⋯ },
  finsetIoo := fun a b =>
    { val := Multiset.ofList (List.range' (instHAdd.hAdd a 1) (instHSub.hSub (instHSub.hSub b a) 1)), nodup := ⋯ },
  finset_mem_Icc := ⋯, finset_mem_Ico := ⋯, finset_mem_Ioc := ⋯, finset_mem_Ioo := ⋯ }
```

### D101: `Nat.instPreorder`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Basic`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D102: `Fin.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `2fb605c17aa879bf453f735ede02a7306496f461d34549bf61cb6c85662ce182`

Type:

```lean
{n : Nat} → (val : Nat) → instLTNat.lt val n → Fin n
```

Fully explicit type:

```lean
{n : Nat} → (val : Nat) → (isLt : @LT.lt.{0} Nat instLTNat val n) → Fin n
```

### D103: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `652ffb54717682f55eafca6c2b47fca31dfea599c9898709ba2f56fbc9113d99`

Type:

```lean
(n m : Nat) → Decidable (instLTNat.lt n m)
```

Fully explicit type:

```lean
(n m : Nat) → Decidable (@LT.lt.{0} Nat instLTNat n m)
```

Definition body (one-level semantic boundary):

```lean
fun n m => n.succ.decLe m
```

### D104: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
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

### D105: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
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
SHA-256: `dc2d7c3bffd501d66aeeb3763f870034f38fb9f081a0690289021fd77e61ca45`

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

/-- Evaluation-order cases discussed after P04 equation (3.4). The `other`
constructor represents any further parenthesization covered by the paper's
unsharpened all-orders bound. -/
inductive P04BlockEvaluationOrder where
  | leftToRight
  | rightToLeft
  | other (code : ℕ)
  deriving DecidableEq

/-- Exact dot product in the block indexing of recurrence (3.1). -/
noncomputable def p04BlockedDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, x k j * y k j

/-- The componentwise scale `|x|ᵀ|y|` in block indexing. -/
noncomputable def p04BlockedAbsDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j|

/-- The row-major equivalence underlying a block partition `n = q*b`. -/
def p04BlockIndexEquiv {n q b : ℕ} (h : n = q * b) :
    Fin q × Fin b ≃ Fin n :=
  finProdFinEquiv.trans (finCongr h.symm)

/-- Flatten one block/local pair through `p04BlockIndexEquiv`. -/
def p04BlockIndex {n q b : ℕ} (h : n = q * b)
    (k : Fin q) (j : Fin b) : Fin n :=
  p04BlockIndexEquiv h (k, j)

/-- Extend a block-indexed error by zero outside its valid natural range. -/
noncomputable def p04ErrorAt {q : ℕ} (error : Fin q → ℝ) (k : ℕ) : ℝ :=
  if h : k < q then error ⟨k, h⟩ else 0

/-- Product of the modeled output-rounding factors from block `k` onward. -/
noncomputable def p04InclusiveErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico k.val q, (1 + p04ErrorAt error l)

/-- Product of the modeled carry factors strictly after block `k`. -/
noncomputable def p04StrictErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico (k.val + 1) q, (1 + p04ErrorAt error l)

/-- A finite-real execution of the scalar recurrence (3.1) underlying P04
Algorithm 3.1.

Each `state_step` is the local standard-model representation (3.2): the old
state and the `b` products carry internal-precision `theta` factors, followed
by the single output-rounding factor `delta`. For the first block, `s₀ = 0`
removes one operation and all term paths fit in `gamma uBar b`; later term
paths fit in `gamma uBar (b+1)`. A generic carry path fits in `gamma uBar b`,
while right-to-left evaluation gives the one-operation carry path responsible
for the `q+b-1` refinement.

The structure contains no compact `alpha`/`beta` witnesses and no final error
bound. Those are consequences of the trace. As in the paper's analysis, the
real-valued local model excludes underflow, overflow, and exceptional IEEE
values and represents the deliberate single-rounding simplification. -/
structure P04BlockFmaDotRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  x : Fin q → Fin b → ℝ
  y : Fin q → Fin b → ℝ
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
  order : P04BlockEvaluationOrder
  state : ℕ → ℝ
  carryTheta : Fin q → ℝ
  termTheta : Fin q → Fin b → ℝ
  delta : Fin q → ℝ
  state_zero : state 0 = 0
  state_step : ∀ k : Fin q,
    state (k.val + 1) =
      (state k.val * (1 + carryTheta k) +
        ∑ j : Fin b, x k j * y k j * (1 + termTheta k j)) *
          (1 + delta k)
  delta_bound : ∀ k,
    |delta k| ≤ p04EffectiveFmaRoundoff uBar uFma uOut
  carry_theta_bound : ∀ k, |carryTheta k| ≤ gamma uBar b
  term_theta_bound : ∀ k j,
    |termTheta k j| ≤ gamma uBar (if k.val = 0 then b else b + 1)
  right_to_left_carry_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k, |carryTheta k| ≤ gamma uBar 1
  innerPathError : Fin q → Fin b → Fin n → ℝ
  inner_path_error_bound : ∀ k j r, |innerPathError k j r| ≤ uBar
  inner_path_factor : ∀ k j,
    (∏ r : Fin n, (1 + innerPathError k j r)) =
      (1 + termTheta k j) * p04StrictErrorProduct carryTheta k
  rightToLeftPathError : Fin q → Fin b → Fin (q + b - 1) → ℝ
  right_to_left_path_error_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j r, |rightToLeftPathError k j r| ≤ uBar
  right_to_left_path_factor :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j,
        (∏ r : Fin (q + b - 1),
          (1 + rightToLeftPathError k j r)) =
            (1 + termTheta k j) *
              p04StrictErrorProduct carryTheta k

/-- The final state of the modeled Algorithm 3.1 scalar recurrence. -/
noncomputable def P04BlockFmaDotRun.computed
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) : ℝ :=
  run.state q

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

/-- A finite-real execution of P04 Algorithm 3.1 for inputs not necessarily
stored in the low precision.

`inputErrorA` and `inputErrorB` give line 1's standard relative-error model.
Every output entry is then the final state of a `P04BlockFmaDotRun`, whose
operands are explicitly linked to the converted row and column. Thus the
structure contains neither the compact `alpha`/`beta` factors nor equation
(3.6); both must be derived from the conversion errors and local block-FMA
traces.

The low/high format constraints express the block-FMA framework on printed
pages C126--C127. All modeled values are finite reals, so the structure has the
paper's stated no-underflow/no-overflow scope and its deliberate
single-rounding simplification. -/
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
  inputErrorA : Fin m → Fin n → ℝ
  inputErrorB : Fin n → Fin t → ℝ
  uLow : ℝ
  uHigh : ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uLow_nonneg : 0 ≤ uLow
  uHigh_nonneg : 0 ≤ uHigh
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uHigh_le_uLow : uHigh ≤ uLow
  uFma_allowed : uFma = uLow ∨ uFma = uHigh
  uOut_allowed : uOut = uLow ∨ uOut = uHigh
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  input_error_A_bound : ∀ i k, |inputErrorA i k| ≤ uLow
  input_error_B_bound : ∀ k j, |inputErrorB k j| ≤ uLow
  entryRun : Fin m → Fin t → P04BlockFmaDotRun n b q
  entry_run_uBar : ∀ i j, (entryRun i j).uBar = uBar
  entry_run_uFma : ∀ i j, (entryRun i j).uFma = uFma
  entry_run_uOut : ∀ i j, (entryRun i j).uOut = uOut
  entry_run_x : ∀ i j k l,
    (entryRun i j).x k l =
      A i (p04BlockIndex inner_partition k l) *
        (1 + inputErrorA i (p04BlockIndex inner_partition k l))
  entry_run_y : ∀ i j k l,
    (entryRun i j).y k l =
      B (p04BlockIndex inner_partition k l) j *
        (1 + inputErrorB (p04BlockIndex inner_partition k l) j)

/-- The componentwise low-precision conversion performed on line 1 of P04
Algorithm 3.1. -/
noncomputable def P04MixedInputMatMulRun.convertedA
    {m n t b1 b b2 p q r : ℕ}
    (run : P04MixedInputMatMulRun m n t b1 b b2 p q r) :
    Fin m → Fin n → ℝ :=
  fun i k => run.A i k * (1 + run.inputErrorA i k)

/-- The analogous line-1 conversion of the right input. -/
noncomputable def P04MixedInputMatMulRun.convertedB
    {m n t b1 b b2 p q r : ℕ}
    (run : P04MixedInputMatMulRun m n t b1 b b2 p q r) :
    Fin n → Fin t → ℝ :=
  fun k j => run.B k j * (1 + run.inputErrorB k j)

/-- The matrix returned by Algorithm 3.1, entrywise defined by the linked
block-FMA traces. -/
noncomputable def P04MixedInputMatMulRun.computed
    {m n t b1 b b2 p q r : ℕ}
    (run : P04MixedInputMatMulRun m n t b1 b b2 p q r) :
    Fin m → Fin t → ℝ :=
  fun i j => (run.entryRun i j).computed

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
