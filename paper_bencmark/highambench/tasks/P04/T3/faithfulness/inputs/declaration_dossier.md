# Declaration dossier for P04-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p04_t3_block_lu_solve_backward_error
    {n b q : ℕ} (run : P04BlockLUSolveRun n b q) :
    ∃ deltaA : Fin n → Fin n → ℝ,
      p04MatVec (run.A + deltaA) run.xHat = run.rhs ∧
      ∀ i j,
        |deltaA i j| ≤
          (p04FactorizationCoeff
              run.uLow run.uBar run.uFma run.uWork q n b +
              2 * gamma run.uWork n + (gamma run.uWork n) ^ 2) *
            p04LUSolveScale run.A run.LHat run.UHat i j
```

## Elaborated target type

```lean
∀ {n b q : Nat} (run : HighamBench.P04BlockLUSolveRun n b q),
  Exists fun deltaA =>
    And (Eq (HighamBench.p04MatVec (instHAdd.hAdd run.A deltaA) run.xHat) run.rhs)
      (∀ (i j : Fin n),
        Real.instLE.le (abs (deltaA i j))
          (instHMul.hMul
            (instHAdd.hAdd
              (instHAdd.hAdd (HighamBench.p04FactorizationCoeff run.uLow run.uBar run.uFma run.uWork q n b)
                (instHMul.hMul 2 (HighamBench.gamma run.uWork n)))
              (instHPow.hPow (HighamBench.gamma run.uWork n) 2))
            (HighamBench.p04LUSolveScale run.A run.LHat run.UHat i j)))
```

## Fully explicit elaborated target type

```lean
∀ {n b q : Nat} (run : HighamBench.P04BlockLUSolveRun n b q),
  @Exists.{1} (Fin n → Fin n → Real) fun (deltaA : Fin n → Fin n → Real) =>
    And
      (@Eq.{1} (Fin n → Real)
        (@HighamBench.p04MatVec n
          (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real) (Fin n → Fin n → Real) (Fin n → Fin n → Real)
            (@instHAdd.{0} (Fin n → Fin n → Real)
              (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Fin n → Real) fun (i : Fin n) =>
                @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real) fun (i : Fin n) => Real.instAdd))
            (@HighamBench.P04BlockLUSolveRun.A n b q run) deltaA)
          (@HighamBench.P04BlockLUSolveRun.xHat n b q run))
        (@HighamBench.P04BlockLUSolveRun.rhs n b q run))
      (∀ (i j : Fin n),
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (deltaA i j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (HighamBench.p04FactorizationCoeff (@HighamBench.P04BlockLUSolveRun.uLow n b q run)
                  (@HighamBench.P04BlockLUSolveRun.uBar n b q run) (@HighamBench.P04BlockLUSolveRun.uFma n b q run)
                  (@HighamBench.P04BlockLUSolveRun.uWork n b q run) q n b)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (HighamBench.gamma (@HighamBench.P04BlockLUSolveRun.uWork n b q run) n)))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                (HighamBench.gamma (@HighamBench.P04BlockLUSolveRun.uWork n b q run) n)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HighamBench.p04LUSolveScale n (@HighamBench.P04BlockLUSolveRun.A n b q run)
              (@HighamBench.P04BlockLUSolveRun.LHat n b q run) (@HighamBench.P04BlockLUSolveRun.UHat n b q run) i j)))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P04Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P04Definitions` imports: `HighamBench.Core`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P04BlockLUSolveRun`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `80db883e5657e19273a16012b2abb259f6ccecd35fc230a392470a361dd051fa`

Type:

```lean
Nat → Nat → Nat → Type
```

Fully explicit type:

```lean
(n b q : Nat) → Type
```

### D002: `HighamBench.P04BlockLUSolveRun.A`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `5f97e026e09d1c559e16e133eacb995aca41c4f0078edec1fa99a5f418dfc167`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.5
```

### D003: `HighamBench.P04BlockLUSolveRun.LHat`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2ca4433178eced08c16ef90aaa319779027fbb0e094c363c4cee3ef51f34a257`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.6
```

### D004: `HighamBench.P04BlockLUSolveRun.UHat`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fa31fc39a21ecb3e381eb99d5021fda149f931d3ecedd803d5c824a6936b7265`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.7
```

### D005: `HighamBench.P04BlockLUSolveRun.rhs`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `ade07b1bb87f4a54cff637a4a17a73fae8f7e79da9e2ef80916223291f585a51`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.30
```

### D006: `HighamBench.P04BlockLUSolveRun.uBar`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `66d8638d5773eb973f7932921004168b5a9d95781bffae969a93f1662cbffdd6`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.13
```

### D007: `HighamBench.P04BlockLUSolveRun.uFma`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `d92d3ac2685e5700a300248e80cdf4f152c7780199029ac371533ece95f16d20`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.14
```

### D008: `HighamBench.P04BlockLUSolveRun.uLow`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `f9dd00bb55a98a6d4586e71aa20e7afe6f9e76bfa7ee6cfc3e9b54a444d11b1f`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.12
```

### D009: `HighamBench.P04BlockLUSolveRun.uWork`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `8ddf3ead49ef537a3c9dcc94894b36680f6f418d4da0f8abcbd165464bb969cb`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.15
```

### D010: `HighamBench.P04BlockLUSolveRun.xHat`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `fbb337629ae64842b228862876c51a11f509e235caedd948a79f03054c084a5d`

Type:

```lean
{n b q : Nat} → HighamBench.P04BlockLUSolveRun n b q → Fin n → Real
```

Fully explicit type:

```lean
{n b q : Nat} → (self : HighamBench.P04BlockLUSolveRun n b q) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n b q self => self.28
```

### D011: `HighamBench.gamma`

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

### D012: `HighamBench.p04FactorizationCoeff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `28b2338fc8565adc5f92aebc03e96d1332f2e62652264b9fb021163961932b5f`

Type:

```lean
Real → Real → Real → Real → Nat → Nat → Nat → Real
```

Fully explicit type:

```lean
(uLow uBar uFma uWork : Real) → (q n b : Nat) → Real
```

Definition body (one-level semantic boundary):

```lean
fun uLow uBar uFma uWork q n b =>
  instHAdd.hAdd (instHAdd.hAdd (instHMul.hMul 2 uLow) (instHPow.hPow uLow 2))
    (instHMul.hMul
      (Real.instMax.max
        (HighamBench.p04BlockFmaCoeff (HighamBench.p04EffectiveFmaRoundoff uBar uFma uWork) uBar (instHSub.hSub q 1)
          (instHAdd.hAdd (instHSub.hSub n b) 1))
        (HighamBench.gamma uWork b))
      (instHPow.hPow (instHAdd.hAdd 1 uLow) 2))
```

### D013: `HighamBench.p04LUSolveScale`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `eb46b47beee11e88ca0d8bc13248f192ab253dccfecab111d671c445075551e5`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A LHat UHat : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A LHat UHat i j => instHAdd.hAdd (abs (A i j)) (HighamBench.p04AbsMatMul LHat UHat i j)
```

### D014: `HighamBench.p04MatVec`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `fcc6c49f75d28a5e1cd319f8faa78701086a74db8b07f8b6e8628c584f9f351c`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Real) → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (A : Fin n → Fin n → Real) → (x : Fin n → Real) → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} A x i => Finset.univ.sum fun j => instHMul.hMul (A i j) (x j)
```

### D015: `HighamBench.P04BlockLUSolveRun.mk`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `5f4b28395b92caf7ca0176dcbdb0bb07ca3a13239e3e6179fff568a4debe27b7`

Type:

```lean
{n b q : Nat} →
  instLTNat.lt 0 n →
    instLTNat.lt 0 b →
      instLTNat.lt 0 q →
        Eq n (instHMul.hMul q b) →
          (A LHat UHat : Fin n → Fin n → Real) →
            HighamBench.p04IsLowerTriangular LHat →
              HighamBench.p04IsUpperTriangular UHat →
                (∀ (i : Fin n), Eq (LHat i i) 1) →
                  (∀ (i : Fin n), Ne (UHat i i) 0) →
                    (uLow uBar uFma uWork : Real) →
                      Real.instLE.le 0 uLow →
                        Real.instLE.le 0 uBar →
                          Real.instLE.le 0 uFma →
                            Real.instLE.le 0 uWork →
                              Real.instLE.le uBar uFma →
                                HighamBench.GammaValid (HighamBench.p04EffectiveFmaRoundoff uBar uFma uWork)
                                    (instHSub.hSub q 1) →
                                  HighamBench.GammaValid uBar (instHAdd.hAdd (instHSub.hSub n b) 1) →
                                    HighamBench.GammaValid uWork b →
                                      HighamBench.GammaValid uWork n →
                                        (factorError : Fin n → Fin n → Real) →
                                          Eq (HighamBench.p04MatMul LHat UHat) (instHAdd.hAdd A factorError) →
                                            (∀ (i j : Fin n),
                                                Real.instLE.le (abs (factorError i j))
                                                  (instHMul.hMul
                                                    (HighamBench.p04FactorizationCoeff uLow uBar uFma uWork q n b)
                                                    (HighamBench.p04LUSolveScale A LHat UHat i j))) →
                                              (xHat yHat rhs : Fin n → Real) →
                                                (deltaL deltaU : Fin n → Fin n → Real) →
                                                  Eq (HighamBench.p04MatVec (instHAdd.hAdd LHat deltaL) yHat) rhs →
                                                    Eq (HighamBench.p04MatVec (instHAdd.hAdd UHat deltaU) xHat) yHat →
                                                      (∀ (i j : Fin n),
                                                          Real.instLE.le (abs (deltaL i j))
                                                            (instHMul.hMul (HighamBench.gamma uWork n)
                                                              (abs (LHat i j)))) →
                                                        (∀ (i j : Fin n),
                                                            Real.instLE.le (abs (deltaU i j))
                                                              (instHMul.hMul (HighamBench.gamma uWork n)
                                                                (abs (UHat i j)))) →
                                                          HighamBench.P04BlockLUSolveRun n b q
```

Fully explicit type:

```lean
{n b q : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (block_size_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b) →
      (block_count_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q) →
        (dimension_eq : @Eq.{1} Nat n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q b)) →
          (A LHat UHat : Fin n → Fin n → Real) →
            (lower_triangular : @HighamBench.p04IsLowerTriangular n LHat) →
              (upper_triangular : @HighamBench.p04IsUpperTriangular n UHat) →
                (lower_unit_diagonal :
                    ∀ (i : Fin n),
                      @Eq.{1} Real (LHat i i)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                  (upper_diagonal_nonzero :
                      ∀ (i : Fin n),
                        @Ne.{1} Real (UHat i i)
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                    (uLow uBar uFma uWork : Real) →
                      (uLow_nonneg :
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uLow) →
                        (uBar_nonneg :
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uBar) →
                          (uFma_nonneg :
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uFma) →
                            (uWork_nonneg :
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) uWork) →
                              (uBar_le_uFma : @LE.le.{0} Real Real.instLE uBar uFma) →
                                (effective_factor_gamma_valid :
                                    HighamBench.GammaValid (HighamBench.p04EffectiveFmaRoundoff uBar uFma uWork)
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) q
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  (internal_factor_gamma_valid :
                                      HighamBench.GammaValid uBar
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n b)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                    (working_block_gamma_valid : HighamBench.GammaValid uWork b) →
                                      (working_solve_gamma_valid : HighamBench.GammaValid uWork n) →
                                        (factorError : Fin n → Fin n → Real) →
                                          (algorithm4_1_factorization :
                                              @Eq.{1} (Fin n → Fin n → Real) (@HighamBench.p04MatMul n LHat UHat)
                                                (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real) (Fin n → Fin n → Real)
                                                  (Fin n → Fin n → Real)
                                                  (@instHAdd.{0} (Fin n → Fin n → Real)
                                                    (@Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Fin n → Real)
                                                      fun (i : Fin n) =>
                                                      @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                        fun (i : Fin n) => Real.instAdd))
                                                  A factorError)) →
                                            (factor_error_bound :
                                                ∀ (i j : Fin n),
                                                  @LE.le.{0} Real Real.instLE
                                                    (@abs.{0} Real Real.lattice Real.instAddGroup (factorError i j))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (HighamBench.p04FactorizationCoeff uLow uBar uFma uWork q n b)
                                                      (@HighamBench.p04LUSolveScale n A LHat UHat i j))) →
                                              (xHat yHat rhs : Fin n → Real) →
                                                (deltaL deltaU : Fin n → Fin n → Real) →
                                                  (forward_substitution :
                                                      @Eq.{1} (Fin n → Real)
                                                        (@HighamBench.p04MatVec n
                                                          (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real)
                                                            (Fin n → Fin n → Real) (Fin n → Fin n → Real)
                                                            (@instHAdd.{0} (Fin n → Fin n → Real)
                                                              (@Pi.instAdd.{0, 0} (Fin n)
                                                                (fun (a : Fin n) => Fin n → Real) fun (i : Fin n) =>
                                                                @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                                  fun (i : Fin n) => Real.instAdd))
                                                            LHat deltaL)
                                                          yHat)
                                                        rhs) →
                                                    (backward_substitution :
                                                        @Eq.{1} (Fin n → Real)
                                                          (@HighamBench.p04MatVec n
                                                            (@HAdd.hAdd.{0, 0, 0} (Fin n → Fin n → Real)
                                                              (Fin n → Fin n → Real) (Fin n → Fin n → Real)
                                                              (@instHAdd.{0} (Fin n → Fin n → Real)
                                                                (@Pi.instAdd.{0, 0} (Fin n)
                                                                  (fun (a : Fin n) => Fin n → Real) fun (i : Fin n) =>
                                                                  @Pi.instAdd.{0, 0} (Fin n) (fun (a : Fin n) => Real)
                                                                    fun (i : Fin n) => Real.instAdd))
                                                              UHat deltaU)
                                                            xHat)
                                                          yHat) →
                                                      (deltaL_bound :
                                                          ∀ (i j : Fin n),
                                                            @LE.le.{0} Real Real.instLE
                                                              (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                (deltaL i j))
                                                              (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                (@instHMul.{0} Real Real.instMul)
                                                                (HighamBench.gamma uWork n)
                                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                  (LHat i j)))) →
                                                        (deltaU_bound :
                                                            ∀ (i j : Fin n),
                                                              @LE.le.{0} Real Real.instLE
                                                                (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                  (deltaU i j))
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (HighamBench.gamma uWork n)
                                                                  (@abs.{0} Real Real.lattice Real.instAddGroup
                                                                    (UHat i j)))) →
                                                          HighamBench.P04BlockLUSolveRun n b q
```

### D016: `HighamBench.p04AbsMatMul`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `076bbab4be5ea220d3df5697e2cfa32e4c8c7eed4134466945d7a8e7409c943b`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → (Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Fully explicit type:

```lean
{n : Nat} → (L U : Fin n → Fin n → Real) → Fin n → Fin n → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} L U i j => Finset.univ.sum fun k => instHMul.hMul (abs (L i k)) (abs (U k j))
```

### D017: `HighamBench.p04BlockFmaCoeff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D018: `HighamBench.p04EffectiveFmaRoundoff`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D019: `HighamBench.p04FactorizationCoeff._proof_1`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `7b8f48496f9b74b3b702884c5b69a9939b93b9c70db21de69d00271603bfb6d4`

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

### D020: `HighamBench.GammaValid`

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

### D021: `HighamBench.p04IsLowerTriangular`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `095cb32b57d06525751a8483bd9a38b38350a8aa27ede0402e46c7c5b5d8f2bb`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (L : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} L => ∀ (i j : Fin n), instLTNat.lt i.val j.val → Eq (L i j) 0
```

### D022: `HighamBench.p04IsUpperTriangular`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `bed459686e88336a212064550d87a25c977aa99c5d466ebeb46c0de76530b86c`

Type:

```lean
{n : Nat} → (Fin n → Fin n → Real) → Prop
```

Fully explicit type:

```lean
{n : Nat} → (U : Fin n → Fin n → Real) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} U => ∀ (i j : Fin n), instLTNat.lt j.val i.val → Eq (U i j) 0
```

### D023: `HighamBench.p04MatMul`

- Role: `local`
- Owner module: `HighamBench.P04Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `6c71297d2486e8ef22f02ec47100b9bbcc0e87cf0e3cdfec01f82b8944677f5a`

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

### D024: `And`

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

### D025: `Eq`

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

### D026: `Exists`

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

### D027: `Fin`

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

### D028: `HAdd.hAdd`

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

### D029: `HMul.hMul`

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

### D030: `HPow.hPow`

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

### D031: `LE.le`

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

### D032: `Monoid.toNatPow`

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

### D033: `Nat`

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

### D034: `Nat.instAtLeastTwoHAddOfNat`

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

### D035: `Nat.instNeZeroSucc`

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

### D036: `OfNat.ofNat`

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

### D037: `Pi.instAdd`

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

### D038: `Real`

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

### D039: `Real.instAdd`

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

### D040: `Real.instAddGroup`

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

### D041: `Real.instLE`

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

### D042: `Real.instMonoid`

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

### D043: `Real.instMul`

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

### D044: `Real.instNatCast`

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

### D045: `Real.lattice`

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

### D046: `abs`

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

### D047: `instHAdd`

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

### D048: `instHMul`

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

### D049: `instHPow`

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

### D050: `instOfNatAtLeastTwo`

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

### D051: `instOfNatNat`

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

### D052: `DivInvMonoid.toDiv`

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

### D053: `Fin.fintype`

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

### D054: `Finset.sum`

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

### D055: `Finset.univ`

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

### D056: `HDiv.hDiv`

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

### D057: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D058: `Max.max`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `6fa198061d1b8595a7b8b0ed74bd9e48f2c7a18aa01bf39d9c30be49c1d4741c`

Type:

```lean
{α : Type u} → [self : Max α] → α → α → α
```

Fully explicit type:

```lean
{α : Type u} → [self : Max.{u} α] → α → α → α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : Max α] => self.1
```

### D059: `Nat.cast`

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

### D060: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D061: `Real.instAddCommMonoid`

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

### D062: `Real.instDivInvMonoid`

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

### D063: `Real.instMax`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `313f6558836157f8e8b4ea7be18fb6953bf9aefc4dcb68940ef5c4889e18a763`

Type:

```lean
Max Real
```

Fully explicit type:

```lean
Max.{0} Real
```

Definition body (one-level semantic boundary):

```lean
{ max := Real.sup✝ }
```

### D064: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D065: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D066: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D067: `instHDiv`

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

### D068: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D069: `instSubNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D070: `LT.lt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D071: `Nat.AtLeastTwo`

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

### D072: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D073: `Real.decidableLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D074: `Real.decidableLT`

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

### D075: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D076: `Real.instZero`

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

### D077: `Zero.toOfNat0`

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

### D078: `instLTNat`

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

### D079: `instMulNat`

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

### D080: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D081: `Fin.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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
