# Declaration dossier for P10-T1

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t1_inherited_right_product_error {n : ℕ}
    (run : P10FirstOrderProductRun n) :
    P10InheritedRightEquation8Term run
```

## Elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P10FirstOrderProductRun n), HighamBench.P10InheritedRightEquation8Term run
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (run : HighamBench.P10FirstOrderProductRun n), @HighamBench.P10InheritedRightEquation8Term n run
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P10Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P10Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Analysis.SpecialFunctions.Log.Base`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P10FirstOrderProductRun`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `9bd1d426161f11499718e2979fa33e1c7138297ee3afab3005ccb07402113235`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D002: `HighamBench.P10InheritedRightEquation8Term`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3ec33566e26fcc11cfd27f8750e897537aef9271e731baf25a8cb7dc33fc6b10`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Prop
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  And
    (Real.instLE.le (run.matrixNorm.value (HighamBench.p10InheritedRightError run))
      (HighamBench.p10InheritedRightErrorContribution run))
    (Eq (HighamBench.p10FirstOrderProductErrorBudget run)
      (instHAdd.hAdd (HighamBench.p10LocalProductErrorContribution run)
        (instHAdd.hAdd (HighamBench.p10InheritedRightErrorContribution run)
          (HighamBench.p10InheritedLeftErrorContribution run))))
```

### D003: `HighamBench.P10ConsistentMatrixNorm.value`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `c89fd5f34b54e0c434c6961a8883fe0f8a1c13fc374f5db43eab50edab3ca849`

Type:

```lean
{n : Nat} → HighamBench.P10ConsistentMatrixNorm n → HighamBench.P10Matrix n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10ConsistentMatrixNorm n) → HighamBench.P10Matrix n → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.1
```

### D004: `HighamBench.P10FirstOrderProductRun.matrixNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `84017a8d3268c796b4fa42d556d7a71fed16c7295b6fd693600c6801252ad236`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → HighamBench.P10ConsistentMatrixNorm n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → HighamBench.P10ConsistentMatrixNorm n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.2
```

### D005: `HighamBench.P10FirstOrderProductRun.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `36f685eb07800f251aeaedfc610e0646b015ed7292248be367df176f3032d245`

Type:

```lean
{n : Nat} →
  instLTNat.lt 0 n →
    (matrixNorm : HighamBench.P10ConsistentMatrixNorm n) →
      (epsilon : Real) →
        Real.instLT.lt 0 epsilon →
          (mu : Nat → Real) →
            (∀ (k : Nat), Real.instLE.le 0 (mu k)) →
              (muDegree : Nat) →
                (muGrowthConstant : Real) →
                  Real.instLE.le 0 muGrowthConstant →
                    (∀ (k : Nat),
                        Real.instLE.le (mu k) (instHMul.hMul muGrowthConstant (instHPow.hPow k.cast muDegree))) →
                      (exactLeft exactRight leftPerturbation rightPerturbation computedProduct localFirstOrderError
                          higherOrderRemainder : HighamBench.P10Matrix n) →
                        (leftInheritedError rightInheritedError : Real) →
                          Real.instLE.le 0 leftInheritedError →
                            Real.instLE.le 0 rightInheritedError →
                              (higherOrderCoeff : Real) →
                                Real.instLE.le 0 higherOrderCoeff →
                                  Eq computedProduct
                                      (instHAdd.hAdd
                                        (instHAdd.hAdd
                                          (HighamBench.p10MatMul n (instHAdd.hAdd exactLeft leftPerturbation)
                                            (instHAdd.hAdd exactRight rightPerturbation))
                                          localFirstOrderError)
                                        higherOrderRemainder) →
                                    Real.instLE.le (matrixNorm.value localFirstOrderError)
                                        (instHMul.hMul
                                          (instHMul.hMul (instHMul.hMul (mu n) epsilon) (matrixNorm.value exactLeft))
                                          (matrixNorm.value exactRight)) →
                                      Real.instLE.le (matrixNorm.value leftPerturbation) leftInheritedError →
                                        Real.instLE.le (matrixNorm.value rightPerturbation) rightInheritedError →
                                          Real.instLE.le (matrixNorm.value higherOrderRemainder)
                                              (instHMul.hMul higherOrderCoeff (instHPow.hPow epsilon 2)) →
                                            HighamBench.P10FirstOrderProductRun n
```

Fully explicit type:

```lean
{n : Nat} →
  (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    (matrixNorm : HighamBench.P10ConsistentMatrixNorm n) →
      (epsilon : Real) →
        (epsilon_pos :
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              epsilon) →
          (mu : Nat → Real) →
            (mu_nonneg :
                ∀ (k : Nat),
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (mu k)) →
              (muDegree : Nat) →
                (muGrowthConstant : Real) →
                  (muGrowthConstant_nonneg :
                      @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) muGrowthConstant) →
                    (mu_polynomial_bound :
                        ∀ (k : Nat),
                          @LE.le.{0} Real Real.instLE (mu k)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muGrowthConstant
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                (@Nat.cast.{0} Real Real.instNatCast k) muDegree))) →
                      (exactLeft exactRight leftPerturbation rightPerturbation computedProduct localFirstOrderError
                          higherOrderRemainder : HighamBench.P10Matrix n) →
                        (leftInheritedError rightInheritedError : Real) →
                          (leftInheritedError_nonneg :
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                leftInheritedError) →
                            (rightInheritedError_nonneg :
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  rightInheritedError) →
                              (higherOrderCoeff : Real) →
                                (higherOrderCoeff_nonneg :
                                    @LE.le.{0} Real Real.instLE
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      higherOrderCoeff) →
                                  (computed_product :
                                      @Eq.{1} (HighamBench.P10Matrix n) computedProduct
                                        (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                          (HighamBench.P10Matrix n)
                                          (@instHAdd.{0} (HighamBench.P10Matrix n)
                                            (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                          (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                            (HighamBench.P10Matrix n)
                                            (@instHAdd.{0} (HighamBench.P10Matrix n)
                                              (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                            (HighamBench.p10MatMul n
                                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                (HighamBench.P10Matrix n)
                                                (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                exactLeft leftPerturbation)
                                              (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                (HighamBench.P10Matrix n)
                                                (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                  (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                exactRight rightPerturbation))
                                            localFirstOrderError)
                                          higherOrderRemainder)) →
                                    (local_error_bound :
                                        @LE.le.{0} Real Real.instLE
                                          (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm localFirstOrderError)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                (mu n) epsilon)
                                              (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm exactLeft))
                                            (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm exactRight))) →
                                      (left_inherited_error_bound :
                                          @LE.le.{0} Real Real.instLE
                                            (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm leftPerturbation)
                                            leftInheritedError) →
                                        (right_inherited_error_bound :
                                            @LE.le.{0} Real Real.instLE
                                              (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm
                                                rightPerturbation)
                                              rightInheritedError) →
                                          (higher_order_bound :
                                              @LE.le.{0} Real Real.instLE
                                                (@HighamBench.P10ConsistentMatrixNorm.value n matrixNorm
                                                  higherOrderRemainder)
                                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                  higherOrderCoeff
                                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                    (@instHPow.{0, 0} Real Nat
                                                      (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                    epsilon
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) →
                                            HighamBench.P10FirstOrderProductRun n
```

### D006: `HighamBench.p10FirstOrderProductErrorBudget`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a9b21bfa1c18fb0bc7815cabd59e2baeaac125064169a9bcfac170ab5979ab3f`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  instHAdd.hAdd
    (instHMul.hMul (instHMul.hMul (instHMul.hMul (run.mu n) run.epsilon) (run.matrixNorm.value run.exactLeft))
      (run.matrixNorm.value run.exactRight))
    (instHAdd.hAdd (instHMul.hMul (run.matrixNorm.value run.exactLeft) run.rightInheritedError)
      (instHMul.hMul run.leftInheritedError (run.matrixNorm.value run.exactRight)))
```

### D007: `HighamBench.p10InheritedLeftErrorContribution`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `0fa06591b26ca24cafaf67943c966f5ca70c04d12e6fdbb5cc7c37022dcb111a`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run => instHMul.hMul run.leftInheritedError (run.matrixNorm.value run.exactRight)
```

### D008: `HighamBench.p10InheritedRightError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `5f0c015537c42b8429712716b1733bf8965d648e46d620a214d7342ca1e85de7`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} run => HighamBench.p10MatMul n run.exactLeft run.rightPerturbation
```

### D009: `HighamBench.p10InheritedRightErrorContribution`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `32702c3450b49e341a62359a3946f67a82c6025be6586fa54b32cb49717d2850`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run => instHMul.hMul (run.matrixNorm.value run.exactLeft) run.rightInheritedError
```

### D010: `HighamBench.p10LocalProductErrorContribution`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `2d82575dbbabb4cfdc57819e5e664f023917285df7b3e8b970e110ee42213e28`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (run : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} run =>
  instHMul.hMul (instHMul.hMul (instHMul.hMul (run.mu n) run.epsilon) (run.matrixNorm.value run.exactLeft))
    (run.matrixNorm.value run.exactRight)
```

### D011: `HighamBench.P10ConsistentMatrixNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `d5666ecf0bcc052280175e10439932d2314385ab2d0efcd8c09449f974582749`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D012: `HighamBench.P10FirstOrderProductRun.epsilon`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d035d77cdd5b477712285af9516534aa4824fd6168ea85feff7484609bb9fd85`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.3
```

### D013: `HighamBench.P10FirstOrderProductRun.exactLeft`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `526a8dcbbf7f622a9d792e1afb665c26afbb504269f128becfd336a1acdd7678`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.11
```

### D014: `HighamBench.P10FirstOrderProductRun.exactRight`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `184721da71f6cae87c9bdcdd375852672a3a723e37466d0e54080d1b9e96f346`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.12
```

### D015: `HighamBench.P10FirstOrderProductRun.leftInheritedError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `0ba09bcbe80565b7a12bf816b9dec646d0f46cc2a06f01d971378473829f0a48`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.18
```

### D016: `HighamBench.P10FirstOrderProductRun.mu`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2b4a0524cb60ddf1b4cd96d8b747266eb3d6885b5573c6311913e12abb800e08`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Nat → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.5
```

### D017: `HighamBench.P10FirstOrderProductRun.rightInheritedError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `57a0b4f418cd235c75eb5eb9a5d237ed9d76155306f61862d212267e96b3eb17`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → Real
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → Real
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.19
```

### D018: `HighamBench.P10FirstOrderProductRun.rightPerturbation`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `fac4a62bd8fdbf974b261c5d84bbf33ef8ccfe7cfaa8146d91651ef6c5dc352d`

Type:

```lean
{n : Nat} → HighamBench.P10FirstOrderProductRun n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} → (self : HighamBench.P10FirstOrderProductRun n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n self => self.14
```

### D019: `HighamBench.P10Matrix`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `4d88fb5bb9dc99cadde8383c8f0b6258d1fba360333ebaa8098421189b8e227f`

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

### D020: `HighamBench.p10MatMul`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8ad7d3a08ebcc065588b98032ed9256d1069c990b9d1ceee50c8f3a660e436e3`

Type:

```lean
(n : Nat) → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
(n : Nat) → (A B : HighamBench.P10Matrix n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun n A B => Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul A B
```

### D021: `HighamBench.P10ConsistentMatrixNorm.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `ec4ccc7a32746513fb4905c50222acec23c72945a45a0cbb5edc31cd563d8f3d`

Type:

```lean
{n : Nat} →
  (value : HighamBench.P10Matrix n → Real) →
    (∀ (A : HighamBench.P10Matrix n), Real.instLE.le 0 (value A)) →
      (∀ (A : HighamBench.P10Matrix n), Iff (Eq (value A) 0) (Eq A 0)) →
        (∀ (c : Real) (A : HighamBench.P10Matrix n),
            Eq (value (instHSMul.hSMul c A)) (instHMul.hMul (abs c) (value A))) →
          (∀ (A B : HighamBench.P10Matrix n),
              Real.instLE.le (value (instHAdd.hAdd A B)) (instHAdd.hAdd (value A) (value B))) →
            (∀ (A B : HighamBench.P10Matrix n),
                Real.instLE.le (value (HighamBench.p10MatMul n A B)) (instHMul.hMul (value A) (value B))) →
              HighamBench.P10ConsistentMatrixNorm n
```

Fully explicit type:

```lean
{n : Nat} →
  (value : HighamBench.P10Matrix n → Real) →
    (value_nonneg :
        ∀ (A : HighamBench.P10Matrix n),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (value A)) →
      (value_eq_zero_iff :
          ∀ (A : HighamBench.P10Matrix n),
            Iff (@Eq.{1} Real (value A) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
              (@Eq.{1} (HighamBench.P10Matrix n) A
                (@OfNat.ofNat.{0} (HighamBench.P10Matrix n) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (HighamBench.P10Matrix n)
                    (@Matrix.zero.{0, 0, 0} (Fin n) (Fin n) Real Real.instZero))))) →
        (value_smul :
            ∀ (c : Real) (A : HighamBench.P10Matrix n),
              @Eq.{1} Real
                (value
                  (@HSMul.hSMul.{0, 0, 0} Real (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                    (@instHSMul.{0, 0} Real (HighamBench.P10Matrix n)
                      (@Matrix.smul.{0, 0, 0, 0} (Fin n) (Fin n) Real Real
                        (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring
                          (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
                          (@Algebra.id.{0} Real Real.instCommSemiring))))
                    c A))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@abs.{0} Real Real.lattice Real.instAddGroup c) (value A))) →
          (value_add_le :
              ∀ (A B : HighamBench.P10Matrix n),
                @LE.le.{0} Real Real.instLE
                  (value
                    (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n) (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                      (@instHAdd.{0} (HighamBench.P10Matrix n)
                        (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                      A B))
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (value A) (value B))) →
            (value_matMul_le :
                ∀ (A B : HighamBench.P10Matrix n),
                  @LE.le.{0} Real Real.instLE (value (HighamBench.p10MatMul n A B))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (value A) (value B))) →
              HighamBench.P10ConsistentMatrixNorm n
```

### D022: `Nat`

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

### D023: `And`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `37ecdc009aa953e3d4924ef10e6a1fb591f6af993cd344fd5a6b5321466517c9`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D024: `Eq`

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

### D025: `HAdd.hAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D026: `LE.le`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D027: `Real`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `38529f0578472feffc4c79d5d0755fa10fc3edafb232ab5e442336d13630ee90`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D028: `Real.instAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D029: `Real.instLE`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D030: `instHAdd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D031: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D032: `HMul.hMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D033: `HPow.hPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D034: `LT.lt`

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

### D035: `Matrix.add`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c5598ac688001263050581cba0ba1df7931dce7913c28fb123463641833aae55`

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

### D036: `Monoid.toNatPow`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D037: `Nat.cast`

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

### D038: `OfNat.ofNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D039: `Real.instLT`

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

### D040: `Real.instMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D041: `Real.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D042: `Real.instNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D043: `Real.instZero`

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

### D044: `Zero.toOfNat0`

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

### D045: `instHMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D046: `instHPow`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D047: `instLTNat`

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

### D048: `instOfNatNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D049: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D050: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D051: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D052: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D053: `Algebra.id`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Algebra.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `5305322be4a562f24a6e568a2b0f4a4e3d7cf5ae9a842e07f0c4058c86e0fc14`

Type:

```lean
(R : Type u) → [inst : CommSemiring R] → Algebra R R
```

Fully explicit type:

```lean
(R : Type u) → [inst : CommSemiring.{u} R] → @Algebra.{u, u} R R inst (@CommSemiring.toSemiring.{u} R inst)
```

Definition body (one-level semantic boundary):

```lean
fun R [CommSemiring R] =>
  let __spread.0 :=
    (have __src := RingHom.id R;
      { toFun := fun x => x, map_one' := ⋯, map_mul' := ⋯, map_zero' := ⋯, map_add' := ⋯ }).toAlgebra;
  let __SMul := instSMulOfMul;
  { toSMul := __SMul, algebraMap := __spread.0.algebraMap, commutes' := ⋯, smul_def' := ⋯ }
```

### D054: `Algebra.toSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Algebra.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7ed84d651a0f6a77f78d6fd14524fe110f2045971d1f824f15cc8f5b8071484f`

Type:

```lean
{R : Type u} → {A : Type v} → {inst : CommSemiring R} → {inst_1 : Semiring A} → [self : Algebra R A] → SMul R A
```

Fully explicit type:

```lean
{R : Type u} →
  {A : Type v} →
    {inst : CommSemiring.{u} R} → {inst_1 : Semiring.{v} A} → [self : @Algebra.{u, v} R A inst inst_1] → SMul.{u, v} R A
```

Definition body (one-level semantic boundary):

```lean
fun R A {inst} {inst_1} [self : Algebra R A] => self.1
```

### D055: `CommSemiring.toSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bcda2e78d6b7602d359ab954baf5c3bd0f6b2503b3ec9a72e1a21a48b9d18d89`

Type:

```lean
{R : Type u} → [self : CommSemiring R] → Semiring R
```

Fully explicit type:

```lean
{R : Type u} → [self : CommSemiring.{u} R] → Semiring.{u} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : CommSemiring R] => self.1
```

### D056: `HSMul.hSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `f1757307432fadbd23925bbf0a318b8da57d17711478e1073a19ce64c21d55f4`

Type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam (Type w)} → [self : HSMul α β γ] → α → β → γ
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → {γ : outParam.{w + 2} (Type w)} → [self : HSMul.{u, v, w} α β γ] → α → β → γ
```

Definition body (one-level semantic boundary):

```lean
fun α β {γ} [self : HSMul α β γ] => self.1
```

### D057: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D058: `Matrix.smul`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `f0a635f6e85a0974e140266364fd7cbf584827ac8183ddf22676b20423399ee8`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {R : Type u_7} → {α : Type v} → [SMul R α] → SMul R (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} →
  {n : Type u_3} →
    {R : Type u_7} → {α : Type v} → [SMul.{u_7, v} R α] → SMul.{u_7, max (max v u_3) u_2} R (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {R} {α} [SMul R α] => Pi.instSMul
```

### D059: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `45e19d9662cc9574dcc02fdb90fcedc0c56420c6369edc144bdd857c8d5e99d4`

Type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero α] → Zero (Matrix m n α)
```

Fully explicit type:

```lean
{m : Type u_2} → {n : Type u_3} → {α : Type v} → [Zero.{v} α] → Zero.{max (max v u_3) u_2} (Matrix.{u_2, u_3, v} m n α)
```

Definition body (one-level semantic boundary):

```lean
fun {m} {n} {α} [Zero α] => Pi.instZero
```

### D060: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D061: `Real.instCommSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `092dfdf642984bd4a336b502f7ac3f87adafd02a6236ba9033e90c0e1439ca7d`

Type:

```lean
CommSemiring Real
```

Fully explicit type:

```lean
CommSemiring.{0} Real
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D062: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D063: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `5`
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

### D064: `instHSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `04ea7c06812eccb8531b763b7aa28fd8f968befff069e74166ff1b406f7512e3`

Type:

```lean
{α : Type u_1} → {β : Type u_2} → [SMul α β] → HSMul α β β
```

Fully explicit type:

```lean
{α : Type u_1} → {β : Type u_2} → [SMul.{u_1, u_2} α β] → HSMul.{u_1, u_2, u_2} α β β
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [inst : SMul α β] => { hSMul := inst.smul }
```
