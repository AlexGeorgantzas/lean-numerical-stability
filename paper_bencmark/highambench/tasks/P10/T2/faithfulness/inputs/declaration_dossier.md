# Declaration dossier for P10-T2

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p10_t2_first_order_product_error {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ epsilon : P10PositiveEpsilon, (epsilon : ℝ) ≤ radius →
          (algorithm.matrixNorm n).value
              (p10ProductFamilyError algorithm family epsilon) ≤
            p10ProductFamilyErrorBudget algorithm family epsilon +
              secondOrderCoeff * (epsilon : ℝ) ^ 2
```

## Elaborated target type

```lean
∀ {n : Nat} (algorithm : HighamBench.P10StableMatrixMultiplication)
  (family : HighamBench.P10FirstOrderProductFamily algorithm n),
  Exists fun secondOrderCoeff =>
    And (Real.instLE.le 0 secondOrderCoeff)
      (Exists fun radius =>
        And (Real.instLT.lt 0 radius)
          (∀ (epsilon : HighamBench.P10PositiveEpsilon),
            Real.instLE.le epsilon.val radius →
              Real.instLE.le
                ((algorithm.matrixNorm n).value (HighamBench.p10ProductFamilyError algorithm family epsilon))
                (instHAdd.hAdd (HighamBench.p10ProductFamilyErrorBudget algorithm family epsilon)
                  (instHMul.hMul secondOrderCoeff (instHPow.hPow epsilon.val 2)))))
```

## Fully explicit elaborated target type

```lean
∀ {n : Nat} (algorithm : HighamBench.P10StableMatrixMultiplication)
  (family : HighamBench.P10FirstOrderProductFamily algorithm n),
  @Exists.{1} Real fun (secondOrderCoeff : Real) =>
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        secondOrderCoeff)
      (@Exists.{1} Real fun (radius : Real) =>
        And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            radius)
          (∀ (epsilon : HighamBench.P10PositiveEpsilon),
            @LE.le.{0} Real Real.instLE
                (@Subtype.val.{1} Real
                  (fun (epsilon : Real) =>
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon)
                  epsilon)
                radius →
              @LE.le.{0} Real Real.instLE
                (@HighamBench.P10ConsistentMatrixNorm.value n
                  (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm n)
                  (@HighamBench.p10ProductFamilyError n algorithm family epsilon))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HighamBench.p10ProductFamilyErrorBudget n algorithm family epsilon)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) secondOrderCoeff
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@Subtype.val.{1} Real
                        (fun (epsilon : Real) =>
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon)
                        epsilon)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P10Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P10Definitions` imports: `HighamBench.Core`, `Mathlib.Analysis.Matrix.Normed`, `Mathlib.Analysis.SpecialFunctions.Log.Base`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P10ConsistentMatrixNorm.value`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D002: `HighamBench.P10FirstOrderProductFamily`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `cbc5462a7c65c3968aceb33ada9714988e4740802dee6f62c84c877cf3661ab2`

Type:

```lean
HighamBench.P10StableMatrixMultiplication → Nat → Type
```

Fully explicit type:

```lean
(algorithm : HighamBench.P10StableMatrixMultiplication) → (n : Nat) → Type
```

### D003: `HighamBench.P10PositiveEpsilon`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `2664f2fe81114472fdd4c541fb7e4356b68164ec7923870e0270fa646aa98910`

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
Subtype fun epsilon => Real.instLT.lt 0 epsilon
```

### D004: `HighamBench.P10StableMatrixMultiplication`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `7a260263cd77e119e5ad8a0a7df1e06b7c41f16f55c045133fe3c68c3ca549cd`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D005: `HighamBench.P10StableMatrixMultiplication.matrixNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `cf75e71c4cc947b23fbf11a667423ac03b9ca441235751f63c83e6b5b88e6279`

Type:

```lean
HighamBench.P10StableMatrixMultiplication → (n : Nat) → HighamBench.P10ConsistentMatrixNorm n
```

Fully explicit type:

```lean
(self : HighamBench.P10StableMatrixMultiplication) → (n : Nat) → HighamBench.P10ConsistentMatrixNorm n
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D006: `HighamBench.p10ProductFamilyError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `a1ce6571e392e12df5fe90655cce4136fa201f2a73a3b20a1ba35182f1f82e2e`

Type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    (family : HighamBench.P10FirstOrderProductFamily algorithm n) →
      (epsilon : HighamBench.P10PositiveEpsilon) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} algorithm family epsilon =>
  instHSub.hSub (HighamBench.p10ProductFamilyComputed algorithm family epsilon)
    (HighamBench.p10MatMul n family.exactLeft family.exactRight)
```

### D007: `HighamBench.p10ProductFamilyErrorBudget`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `73fa33bd3fc9c4bcd7d0fea2a6bc80c817f5c467702ae19c725203cff277f838`

Type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → Real
```

Fully explicit type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    (family : HighamBench.P10FirstOrderProductFamily algorithm n) → (epsilon : HighamBench.P10PositiveEpsilon) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} algorithm family epsilon =>
  instHAdd.hAdd
    (instHMul.hMul
      (instHMul.hMul (instHMul.hMul (algorithm.mu n) epsilon.val) ((algorithm.matrixNorm n).value family.exactLeft))
      ((algorithm.matrixNorm n).value family.exactRight))
    (instHAdd.hAdd
      (instHMul.hMul ((algorithm.matrixNorm n).value family.exactLeft) (family.rightInheritedError epsilon))
      (instHMul.hMul (family.leftInheritedError epsilon) ((algorithm.matrixNorm n).value family.exactRight)))
```

### D008: `HighamBench.P10ConsistentMatrixNorm`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `d5666ecf0bcc052280175e10439932d2314385ab2d0efcd8c09449f974582749`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D009: `HighamBench.P10FirstOrderProductFamily.exactLeft`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `8f75c64d615703b1463df7d13205e1cab01ed0022e2b42703eed344eaa30be97`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → (self : HighamBench.P10FirstOrderProductFamily algorithm n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.2
```

### D010: `HighamBench.P10FirstOrderProductFamily.exactRight`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `23a4702fb90ea4b64602f5d7012b33631a7153d7068067cec264e1b2715ea8ee`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → (self : HighamBench.P10FirstOrderProductFamily algorithm n) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.3
```

### D011: `HighamBench.P10FirstOrderProductFamily.leftInheritedError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b36068b1b2c9bc9811e4ba32e75215dccb4d1e37124bbe4e1d590e40aaf8cf9c`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → Real
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → (self : HighamBench.P10FirstOrderProductFamily algorithm n) → HighamBench.P10PositiveEpsilon → Real
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.6
```

### D012: `HighamBench.P10FirstOrderProductFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `95424dc710c9de417c196befaecbfab974e754f12a19e771684444d9e8ad5e34`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    instLTNat.lt 0 n →
      (exactLeft exactRight : HighamBench.P10Matrix n) →
        (leftPerturbation rightPerturbation : HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n) →
          (leftInheritedError rightInheritedError : HighamBench.P10PositiveEpsilon → Real) →
            (∀ (epsilon : HighamBench.P10PositiveEpsilon), Real.instLE.le 0 (leftInheritedError epsilon)) →
              (∀ (epsilon : HighamBench.P10PositiveEpsilon), Real.instLE.le 0 (rightInheritedError epsilon)) →
                (leftInheritedCoeff rightInheritedCoeff : Real) →
                  Real.instLE.le 0 leftInheritedCoeff →
                    Real.instLE.le 0 rightInheritedCoeff →
                      (localSecondOrderCoeff : Real) →
                        Real.instLE.le 0 localSecondOrderCoeff →
                          (radius : Real) →
                            Real.instLT.lt 0 radius →
                              (∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                  Real.instLE.le ((algorithm.matrixNorm n).value (leftPerturbation epsilon))
                                    (leftInheritedError epsilon)) →
                                (∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                    Real.instLE.le ((algorithm.matrixNorm n).value (rightPerturbation epsilon))
                                      (rightInheritedError epsilon)) →
                                  (∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                      Real.instLE.le epsilon.val radius →
                                        Real.instLE.le (leftInheritedError epsilon)
                                          (instHMul.hMul leftInheritedCoeff epsilon.val)) →
                                    (∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                        Real.instLE.le epsilon.val radius →
                                          Real.instLE.le (rightInheritedError epsilon)
                                            (instHMul.hMul rightInheritedCoeff epsilon.val)) →
                                      (∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                          Real.instLE.le epsilon.val radius →
                                            Real.instLE.le
                                              ((algorithm.matrixNorm n).value
                                                (instHSub.hSub
                                                  (algorithm.product n epsilon
                                                    (instHAdd.hAdd exactLeft (leftPerturbation epsilon))
                                                    (instHAdd.hAdd exactRight (rightPerturbation epsilon)))
                                                  (HighamBench.p10MatMul n
                                                    (instHAdd.hAdd exactLeft (leftPerturbation epsilon))
                                                    (instHAdd.hAdd exactRight (rightPerturbation epsilon)))))
                                              (instHAdd.hAdd
                                                (instHMul.hMul
                                                  (instHMul.hMul (instHMul.hMul (algorithm.mu n) epsilon.val)
                                                    ((algorithm.matrixNorm n).value exactLeft))
                                                  ((algorithm.matrixNorm n).value exactRight))
                                                (instHMul.hMul localSecondOrderCoeff (instHPow.hPow epsilon.val 2)))) →
                                        HighamBench.P10FirstOrderProductFamily algorithm n
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    (dimension_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
      (exactLeft exactRight : HighamBench.P10Matrix n) →
        (leftPerturbation rightPerturbation : HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n) →
          (leftInheritedError rightInheritedError : HighamBench.P10PositiveEpsilon → Real) →
            (leftInheritedError_nonneg :
                ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (leftInheritedError epsilon)) →
              (rightInheritedError_nonneg :
                  ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (rightInheritedError epsilon)) →
                (leftInheritedCoeff rightInheritedCoeff : Real) →
                  (leftInheritedCoeff_nonneg :
                      @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                        leftInheritedCoeff) →
                    (rightInheritedCoeff_nonneg :
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          rightInheritedCoeff) →
                      (localSecondOrderCoeff : Real) →
                        (localSecondOrderCoeff_nonneg :
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              localSecondOrderCoeff) →
                          (radius : Real) →
                            (radius_pos :
                                @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) radius) →
                              (left_perturbation_bound :
                                  ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                    @LE.le.{0} Real Real.instLE
                                      (@HighamBench.P10ConsistentMatrixNorm.value n
                                        (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm n)
                                        (leftPerturbation epsilon))
                                      (leftInheritedError epsilon)) →
                                (right_perturbation_bound :
                                    ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                      @LE.le.{0} Real Real.instLE
                                        (@HighamBench.P10ConsistentMatrixNorm.value n
                                          (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm n)
                                          (rightPerturbation epsilon))
                                        (rightInheritedError epsilon)) →
                                  (left_inherited_first_order :
                                      ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                        @LE.le.{0} Real Real.instLE
                                            (@Subtype.val.{1} Real
                                              (fun (epsilon : Real) =>
                                                @LT.lt.{0} Real Real.instLT
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  epsilon)
                                              epsilon)
                                            radius →
                                          @LE.le.{0} Real Real.instLE (leftInheritedError epsilon)
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              leftInheritedCoeff
                                              (@Subtype.val.{1} Real
                                                (fun (epsilon : Real) =>
                                                  @LT.lt.{0} Real Real.instLT
                                                    (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                      (@Zero.toOfNat0.{0} Real Real.instZero))
                                                    epsilon)
                                                epsilon))) →
                                    (right_inherited_first_order :
                                        ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                          @LE.le.{0} Real Real.instLE
                                              (@Subtype.val.{1} Real
                                                (fun (epsilon : Real) =>
                                                  @LT.lt.{0} Real Real.instLT
                                                    (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                      (@Zero.toOfNat0.{0} Real Real.instZero))
                                                    epsilon)
                                                epsilon)
                                              radius →
                                            @LE.le.{0} Real Real.instLE (rightInheritedError epsilon)
                                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                rightInheritedCoeff
                                                (@Subtype.val.{1} Real
                                                  (fun (epsilon : Real) =>
                                                    @LT.lt.{0} Real Real.instLT
                                                      (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                        (@Zero.toOfNat0.{0} Real Real.instZero))
                                                      epsilon)
                                                  epsilon))) →
                                      (local_error_bound :
                                          ∀ (epsilon : HighamBench.P10PositiveEpsilon),
                                            @LE.le.{0} Real Real.instLE
                                                (@Subtype.val.{1} Real
                                                  (fun (epsilon : Real) =>
                                                    @LT.lt.{0} Real Real.instLT
                                                      (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                        (@Zero.toOfNat0.{0} Real Real.instZero))
                                                      epsilon)
                                                  epsilon)
                                                radius →
                                              @LE.le.{0} Real Real.instLE
                                                (@HighamBench.P10ConsistentMatrixNorm.value n
                                                  (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm n)
                                                  (@HSub.hSub.{0, 0, 0} (HighamBench.P10Matrix n)
                                                    (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                    (@instHSub.{0} (HighamBench.P10Matrix n)
                                                      (@Matrix.sub.{0, 0, 0} (Fin n) (Fin n) Real Real.instSub))
                                                    (HighamBench.P10StableMatrixMultiplication.product algorithm n
                                                      epsilon
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n)
                                                        (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                        (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                          (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                        exactLeft (leftPerturbation epsilon))
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n)
                                                        (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                        (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                          (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                        exactRight (rightPerturbation epsilon)))
                                                    (HighamBench.p10MatMul n
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n)
                                                        (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                        (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                          (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                        exactLeft (leftPerturbation epsilon))
                                                      (@HAdd.hAdd.{0, 0, 0} (HighamBench.P10Matrix n)
                                                        (HighamBench.P10Matrix n) (HighamBench.P10Matrix n)
                                                        (@instHAdd.{0} (HighamBench.P10Matrix n)
                                                          (@Matrix.add.{0, 0, 0} (Fin n) (Fin n) Real Real.instAdd))
                                                        exactRight (rightPerturbation epsilon)))))
                                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@HMul.hMul.{0, 0, 0} Real Real Real
                                                        (@instHMul.{0} Real Real.instMul)
                                                        (HighamBench.P10StableMatrixMultiplication.mu algorithm n)
                                                        (@Subtype.val.{1} Real
                                                          (fun (epsilon : Real) =>
                                                            @LT.lt.{0} Real Real.instLT
                                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                                              epsilon)
                                                          epsilon))
                                                      (@HighamBench.P10ConsistentMatrixNorm.value n
                                                        (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm
                                                          n)
                                                        exactLeft))
                                                    (@HighamBench.P10ConsistentMatrixNorm.value n
                                                      (HighamBench.P10StableMatrixMultiplication.matrixNorm algorithm n)
                                                      exactRight))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    localSecondOrderCoeff
                                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                                      (@instHPow.{0, 0} Real Nat
                                                        (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                                      (@Subtype.val.{1} Real
                                                        (fun (epsilon : Real) =>
                                                          @LT.lt.{0} Real Real.instLT
                                                            (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                              (@Zero.toOfNat0.{0} Real Real.instZero))
                                                            epsilon)
                                                        epsilon)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                        (instOfNatNat (nat_lit 2))))))) →
                                        HighamBench.P10FirstOrderProductFamily algorithm n
```

### D013: `HighamBench.P10FirstOrderProductFamily.rightInheritedError`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `5564d33fddad101da543d97b24e62c701aa8f62817cb2dc3d4652708122d11de`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → Real
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} → (self : HighamBench.P10FirstOrderProductFamily algorithm n) → HighamBench.P10PositiveEpsilon → Real
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.7
```

### D014: `HighamBench.P10Matrix`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
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

### D015: `HighamBench.P10StableMatrixMultiplication.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `84232f1a98567f4ccbadd679b1f1ddf56b99e3e5bf7f5fb85666385ae9316fb8`

Type:

```lean
((n : Nat) → HighamBench.P10ConsistentMatrixNorm n) →
  (mu : Nat → Real) →
    (∀ (n : Nat), Real.instLE.le 0 (mu n)) →
      (muDegree : Nat) →
        (muGrowthConstant : Real) →
          Real.instLE.le 0 muGrowthConstant →
            (∀ (n : Nat),
                instLTNat.lt 0 n →
                  Real.instLE.le (mu n) (instHMul.hMul muGrowthConstant (instHPow.hPow n.cast muDegree))) →
              ((n : Nat) →
                  HighamBench.P10PositiveEpsilon →
                    HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n) →
                HighamBench.P10StableMatrixMultiplication
```

Fully explicit type:

```lean
(matrixNorm : (n : Nat) → HighamBench.P10ConsistentMatrixNorm n) →
  (mu : Nat → Real) →
    (mu_nonneg :
        ∀ (n : Nat),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (mu n)) →
      (muDegree : Nat) →
        (muGrowthConstant : Real) →
          (muGrowthConstant_nonneg :
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                muGrowthConstant) →
            (mu_polynomial_bound :
                ∀ (n : Nat),
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
                    @LE.le.{0} Real Real.instLE (mu n)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) muGrowthConstant
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast n) muDegree))) →
              (product :
                  (n : Nat) →
                    HighamBench.P10PositiveEpsilon →
                      HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n) →
                HighamBench.P10StableMatrixMultiplication
```

### D016: `HighamBench.P10StableMatrixMultiplication.mu`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `74ea9f8b488e3d32bdceb5606495da6f51297b4a5022379e5580e107caeab5a8`

Type:

```lean
HighamBench.P10StableMatrixMultiplication → Nat → Real
```

Fully explicit type:

```lean
(self : HighamBench.P10StableMatrixMultiplication) → Nat → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D017: `HighamBench.p10MatMul`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D018: `HighamBench.p10ProductFamilyComputed`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a5cbc54ab01794bc70f6101676d112c10fa5114d17241b16b46209a4de4303d5`

Type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{n : Nat} →
  (algorithm : HighamBench.P10StableMatrixMultiplication) →
    (family : HighamBench.P10FirstOrderProductFamily algorithm n) →
      (epsilon : HighamBench.P10PositiveEpsilon) → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun {n} algorithm family epsilon =>
  algorithm.product n epsilon (instHAdd.hAdd family.exactLeft (family.leftPerturbation epsilon))
    (instHAdd.hAdd family.exactRight (family.rightPerturbation epsilon))
```

### D019: `HighamBench.P10ConsistentMatrixNorm.mk`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `constructor`
- Distance from target type: `3`
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

### D020: `HighamBench.P10FirstOrderProductFamily.leftPerturbation`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `462df35cc46da2cdd17170c4d93fc473f67b56f0dbaa8a107b2b7756cdfd643f`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    (self : HighamBench.P10FirstOrderProductFamily algorithm n) →
      HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.4
```

### D021: `HighamBench.P10FirstOrderProductFamily.rightPerturbation`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c4504c0c4a6bcd8d8d696fbb9bfa7ecca9676ddb2258f30d3204bad0dd4ccc78`

Type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    HighamBench.P10FirstOrderProductFamily algorithm n → HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
{algorithm : HighamBench.P10StableMatrixMultiplication} →
  {n : Nat} →
    (self : HighamBench.P10FirstOrderProductFamily algorithm n) →
      HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun algorithm n self => self.5
```

### D022: `HighamBench.P10StableMatrixMultiplication.product`

- Role: `local`
- Owner module: `HighamBench.P10Definitions`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `2330d9e873aec0f7171f5a03613ad73d85eb3a6efd009b8ed92f9b23999a8fb6`

Type:

```lean
HighamBench.P10StableMatrixMultiplication →
  (n : Nat) →
    HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n
```

Fully explicit type:

```lean
(self : HighamBench.P10StableMatrixMultiplication) →
  (n : Nat) →
    HighamBench.P10PositiveEpsilon → HighamBench.P10Matrix n → HighamBench.P10Matrix n → HighamBench.P10Matrix n
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D023: `And`

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

### D024: `Exists`

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

### D025: `HAdd.hAdd`

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

### D026: `HMul.hMul`

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

### D027: `HPow.hPow`

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

### D028: `LE.le`

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

### D029: `LT.lt`

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

### D030: `Monoid.toNatPow`

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

### D031: `Nat`

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

### D032: `OfNat.ofNat`

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

### D033: `Real`

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

### D034: `Real.instAdd`

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

### D035: `Real.instLE`

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

### D036: `Real.instLT`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D037: `Real.instMonoid`

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

### D038: `Real.instMul`

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

### D039: `Real.instZero`

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

### D040: `Subtype.val`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `69c61ab82498e5563eaf5f0313ea7f2164c284c3dc742024a30332372a46663d`

Type:

```lean
{α : Sort u} → {p : α → Prop} → Subtype p → α
```

Fully explicit type:

```lean
{α : Sort u} → {p : α → Prop} → (self : @Subtype.{u} α p) → α
```

Definition body (one-level semantic boundary):

```lean
fun α p self => self.1
```

### D041: `Zero.toOfNat0`

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

### D042: `instHAdd`

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

### D043: `instHMul`

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

### D044: `instHPow`

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

### D045: `instOfNatNat`

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

### D046: `Fin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `59788903be5da78a88e4dc3844df38effdaabdfa82bb364602790d2271da7fda`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
(n : Nat) → Type
```

### D047: `HSub.hSub`

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

### D048: `Matrix.sub`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f9a0c1f5b41c8d9a8658798c73b295495f6dfbf0bd7d081817aec4f598bbfc46`

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

### D049: `Real.instSub`

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

### D050: `Subtype`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `3b0bb8433bd0c981dbdb4d6256bf74c50e9883207dae8d309dcb705135cf932c`

Type:

```lean
{α : Sort u} → (α → Prop) → Sort (max 1 u)
```

Fully explicit type:

```lean
{α : Sort u} → (p : α → Prop) → Sort (max 1 u)
```

### D051: `instHSub`

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

### D052: `Fin.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D053: `Matrix`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D054: `Matrix.add`

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

### D055: `Matrix.instHMulOfFintypeOfMulOfAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Matrix.Mul`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D056: `Nat.cast`

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

### D057: `Real.instAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D058: `Real.instNatCast`

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

### D060: `Algebra.id`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Algebra.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D061: `Algebra.toSMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Algebra.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D062: `CommSemiring.toSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D063: `Eq`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `63e9afa87e04d13393a2fe09e8e76489d96be3982734b4b40a52fc6ebea863d7`

Type:

```lean
{α : Sort u_1} → α → α → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → α → α → Prop
```

### D064: `HSMul.hSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
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

### D065: `Iff`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `b9f48489cd9ca513eeae7e3e4fb154f354b93867eda8b67d1630275c4cb4f30b`

Type:

```lean
Prop → Prop → Prop
```

Fully explicit type:

```lean
(a b : Prop) → Prop
```

### D066: `Matrix.smul`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D067: `Matrix.zero`

- Role: `external-frontier`
- Owner module: `Mathlib.LinearAlgebra.Matrix.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D068: `Real.instAddGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D069: `Real.instCommSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D070: `Real.lattice`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D071: `abs`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Order.Group.Unbundled.Abs`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D072: `instHSMul`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### `HighamBench.P10Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P10Definitions.lean`
SHA-256: `51ea90c955e708bcf5681be646793c317f1d15f5e33aaa7cb2e1593acd55d94a`

```lean
import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- A square real matrix in the native finite `Matrix` representation. -/
abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite square matrix multiplication. -/
noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

/-- The Frobenius norm, written explicitly to keep the public statement lightweight. -/
noncomputable def p10FrobNorm {n : ℕ} (A : P10Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- An otherwise unspecified matrix norm with the consistency properties used
in the paper's normwise product analysis. -/
structure P10ConsistentMatrixNorm (n : ℕ) where
  value : P10Matrix n → ℝ
  value_nonneg : ∀ A, 0 ≤ value A
  value_eq_zero_iff : ∀ A, value A = 0 ↔ A = 0
  value_smul : ∀ (c : ℝ) A, value (c • A) = |c| * value A
  value_add_le : ∀ A B, value (A + B) ≤ value A + value B
  value_matMul_le : ∀ A B,
    value (p10MatMul n A B) ≤ value A * value B

/-- One stable matrix-product computation with inherited operand errors.  The
cross term and the local higher-order remainder are retained in the execution
model but excluded from its first-order error. -/
structure P10FirstOrderProductRun (n : ℕ) where
  dimension_pos : 0 < n
  matrixNorm : P10ConsistentMatrixNorm n
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mu : ℕ → ℝ
  mu_nonneg : ∀ k, 0 ≤ mu k
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10Matrix n
  rightPerturbation : P10Matrix n
  computedProduct : P10Matrix n
  localFirstOrderError : P10Matrix n
  higherOrderRemainder : P10Matrix n
  leftInheritedError : ℝ
  rightInheritedError : ℝ
  leftInheritedError_nonneg : 0 ≤ leftInheritedError
  rightInheritedError_nonneg : 0 ≤ rightInheritedError
  computed_product :
    computedProduct =
      p10MatMul n
          (exactLeft + leftPerturbation)
          (exactRight + rightPerturbation) +
        localFirstOrderError + higherOrderRemainder
  local_error_bound :
    matrixNorm.value localFirstOrderError ≤
      mu n * epsilon * matrixNorm.value exactLeft * matrixNorm.value exactRight
  left_inherited_error_bound :
    matrixNorm.value leftPerturbation ≤ leftInheritedError
  right_inherited_error_bound :
    matrixNorm.value rightPerturbation ≤ rightInheritedError

/-- The realized product error with the inherited cross term and the local
higher-order remainder removed, exactly as required by first-order analysis. -/
noncomputable def p10FirstOrderProductError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  run.computedProduct - p10MatMul n run.exactLeft run.exactRight -
      p10MatMul n run.leftPerturbation run.rightPerturbation -
    run.higherOrderRemainder

/-- The three first-order contributions printed in equation (8). -/
noncomputable def p10FirstOrderProductErrorBudget {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
      run.matrixNorm.value run.exactRight +
    (run.matrixNorm.value run.exactLeft * run.rightInheritedError +
      run.leftInheritedError * run.matrixNorm.value run.exactRight)

/-- The inherited-right error matrix produced to first order by multiplying
the right operand perturbation on the left by the exact left operand. -/
noncomputable def p10InheritedRightError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.exactLeft run.rightPerturbation

/-- The inherited-left error matrix produced to first order by multiplying
the left operand perturbation by the exact right operand. -/
noncomputable def p10InheritedLeftError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.leftPerturbation run.exactRight

/-- Equation (8)'s local stable-multiplication contribution. -/
noncomputable def p10LocalProductErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
    run.matrixNorm.value run.exactRight

/-- Equation (8)'s inherited-right contribution `||A||*err(B,n)`. -/
noncomputable def p10InheritedRightErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.matrixNorm.value run.exactLeft * run.rightInheritedError

/-- Equation (8)'s inherited-left contribution `err(A,n)*||B||`. -/
noncomputable def p10InheritedLeftErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.leftInheritedError * run.matrixNorm.value run.exactRight

/-- The selected inherited-right term. The first conjunct links all three
first-order matrices to the realized product error; the second gives equation
`(8)`'s `||A||*err(B,n)` bound for the middle matrix. -/
def P10InheritedRightEquation8Term {n : ℕ}
    (run : P10FirstOrderProductRun n) : Prop :=
  p10FirstOrderProductError run =
      run.localFirstOrderError +
        (p10InheritedRightError run + p10InheritedLeftError run) ∧
    run.matrixNorm.value (p10InheritedRightError run) ≤
      p10InheritedRightErrorContribution run

/-! ## Uniform stable-product model for equation (8) -/

/-- A positive machine precision. Quantifying over this type makes the
`O(epsilon^2)` term in the paper's first-order analysis uniform as epsilon
tends to zero through positive values. -/
abbrev P10PositiveEpsilon := {epsilon : ℝ // 0 < epsilon}

/-- One matrix-multiplication algorithm, with the norm and polynomially
bounded stability factor fixed across dimensions, inputs, and precisions. -/
structure P10StableMatrixMultiplication where
  matrixNorm : (n : ℕ) → P10ConsistentMatrixNorm n
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  product : (n : ℕ) → P10PositiveEpsilon →
    P10Matrix n → P10Matrix n → P10Matrix n

/-- An epsilon-indexed family of calls to one stable multiplication
algorithm. The local certificate is equation (1), after absorbing the
first-order change from perturbed operands into one uniform quadratic term.
The inherited errors themselves are required to be uniformly first order. -/
structure P10FirstOrderProductFamily
    (algorithm : P10StableMatrixMultiplication) (n : ℕ) where
  dimension_pos : 0 < n
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10PositiveEpsilon → P10Matrix n
  rightPerturbation : P10PositiveEpsilon → P10Matrix n
  leftInheritedError : P10PositiveEpsilon → ℝ
  rightInheritedError : P10PositiveEpsilon → ℝ
  leftInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ leftInheritedError epsilon
  rightInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ rightInheritedError epsilon
  leftInheritedCoeff : ℝ
  rightInheritedCoeff : ℝ
  leftInheritedCoeff_nonneg : 0 ≤ leftInheritedCoeff
  rightInheritedCoeff_nonneg : 0 ≤ rightInheritedCoeff
  localSecondOrderCoeff : ℝ
  localSecondOrderCoeff_nonneg : 0 ≤ localSecondOrderCoeff
  radius : ℝ
  radius_pos : 0 < radius
  left_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (leftPerturbation epsilon) ≤
      leftInheritedError epsilon
  right_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (rightPerturbation epsilon) ≤
      rightInheritedError epsilon
  left_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    leftInheritedError epsilon ≤ leftInheritedCoeff * (epsilon : ℝ)
  right_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    rightInheritedError epsilon ≤ rightInheritedCoeff * (epsilon : ℝ)
  local_error_bound : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    (algorithm.matrixNorm n).value
        (algorithm.product n epsilon
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon) -
          p10MatMul n
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon)) ≤
      algorithm.mu n * (epsilon : ℝ) *
          (algorithm.matrixNorm n).value exactLeft *
          (algorithm.matrixNorm n).value exactRight +
        localSecondOrderCoeff * (epsilon : ℝ) ^ 2

/-- The actual output of the fixed multiplication algorithm on the two
epsilon-dependent computed operands. -/
noncomputable def p10ProductFamilyComputed {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  algorithm.product n epsilon
    (family.exactLeft + family.leftPerturbation epsilon)
    (family.exactRight + family.rightPerturbation epsilon)

/-- The actual product error. No inherited cross term or local remainder is
removed from this quantity. -/
noncomputable def p10ProductFamilyError {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  p10ProductFamilyComputed algorithm family epsilon -
    p10MatMul n family.exactLeft family.exactRight

/-- The three leading contributions printed in equation (8). -/
noncomputable def p10ProductFamilyErrorBudget {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : ℝ :=
  algorithm.mu n * (epsilon : ℝ) *
      (algorithm.matrixNorm n).value family.exactLeft *
      (algorithm.matrixNorm n).value family.exactRight +
    ((algorithm.matrixNorm n).value family.exactLeft *
        family.rightInheritedError epsilon +
      family.leftInheritedError epsilon *
        (algorithm.matrixNorm n).value family.exactRight)

/-- The one-level amplification factor in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterGrowth {n : ℕ}
    (A B : P10Matrix n) (sep : ℝ) : ℝ :=
  4 + 2 * (p10FrobNorm A + p10FrobNorm B) / sep

/-- The one-level forcing term in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterForcing {n : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ) : ℝ :=
  epsilon / sep *
    (3 * p10FrobNorm C +
      2 * mu * (p10FrobNorm A + p10FrobNorm B) * p10FrobNorm R)

/-! ## Recursive Sylvester solver model -/

/-- Recursive index set for a matrix of dimension exactly `2^depth`. -/
def P10DyadicIndex : ℕ → Type
  | 0 => Fin 1
  | depth + 1 => P10DyadicIndex depth ⊕ P10DyadicIndex depth

noncomputable instance p10DyadicIndexFintype (depth : ℕ) :
    Fintype (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : Fintype (P10DyadicIndex depth) := ih
      infer_instance

noncomputable instance p10DyadicIndexDecidableEq (depth : ℕ) :
    DecidableEq (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : DecidableEq (P10DyadicIndex depth) := ih
      infer_instance

/-- A square real matrix of power-of-two dimension. -/
abbrev P10DyadicMatrix (depth : ℕ) :=
  Matrix (P10DyadicIndex depth) (P10DyadicIndex depth) ℝ

/-- The Frobenius norm used in the paper's definition of `sep(A,B)`. -/
noncomputable def p10DyadicFrobNorm {depth : ℕ}
    (A : P10DyadicMatrix depth) : ℝ :=
  letI : NormedRing (P10DyadicMatrix depth) :=
    Matrix.frobeniusNormedRing
  ‖A‖

noncomputable def p10DyadicBlock11 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₁ A

noncomputable def p10DyadicBlock12 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₂ A

noncomputable def p10DyadicBlock21 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₁ A

noncomputable def p10DyadicBlock22 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₂ A

/-- The Sylvester operator `X ↦ A*X-X*B`. -/
noncomputable def p10SylvesterAction {depth : ℕ}
    (A B X : P10DyadicMatrix depth) : P10DyadicMatrix depth :=
  A * X - X * B

/-- Certificate for the Frobenius variational definition of `sep(A,B)`. -/
structure P10SylvesterSeparation {depth : ℕ}
    (A B : P10DyadicMatrix depth) where
  value : ℝ
  value_pos : 0 < value
  lower_bound : ∀ X,
    value * p10DyadicFrobNorm X ≤
      p10DyadicFrobNorm (p10SylvesterAction A B X)
  attained : ∃ X,
    p10DyadicFrobNorm X = 1 ∧
      p10DyadicFrobNorm (p10SylvesterAction A B X) = value

/-- One exact Sylvester problem and its first-order computed SylR result.
Real-valued states model the standard finite regime: exceptional values and
the higher-order terms suppressed by the paper are outside this certificate. -/
structure P10SylRProblem (depth : ℕ) where
  A : P10DyadicMatrix depth
  B : P10DyadicMatrix depth
  C : P10DyadicMatrix depth
  exactSolution : P10DyadicMatrix depth
  computedSolution : P10DyadicMatrix depth
  exact_equation :
    p10SylvesterAction A B exactSolution = -C
  separation : P10SylvesterSeparation A B

/-- Absolute Frobenius forward error in the paper's first-order model. -/
noncomputable def p10SylRForwardError {depth : ℕ}
    (problem : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm (problem.computedSolution - problem.exactSolution)

noncomputable def p10SylRExactRhs11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock11 parent.C +
    p10DyadicBlock12 parent.A * p10DyadicBlock21 parent.exactSolution

noncomputable def p10SylRExactRhs22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock22 parent.C -
    p10DyadicBlock21 parent.exactSolution * p10DyadicBlock12 parent.B

noncomputable def p10SylRExactRhs12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock12 parent.C -
      p10DyadicBlock11 parent.exactSolution * p10DyadicBlock12 parent.B +
    p10DyadicBlock12 parent.A * p10DyadicBlock22 parent.exactSolution

/-- Total error in a computed child block, measured against the corresponding
block of the exact parent solution.  This includes rounded-RHS error. -/
noncomputable def p10SylRBlockError21 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock21 parent.exactSolution)

noncomputable def p10SylRBlockError11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock11 parent.exactSolution)

noncomputable def p10SylRBlockError22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock22 parent.exactSolution)

noncomputable def p10SylRBlockError12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock12 parent.exactSolution)

/-- One non-base SylR node and the four page-86 first-order block estimates.
The fields expose the solve order `R21`, `R11`, `R22`, `R12`, exact right-hand
sides (15)--(18), product model (8), and separation inequality (19). -/
structure P10SylRLevelCertificate {depth : ℕ}
    (epsilon muHalf smallerError globalANorm globalBNorm globalCNorm
      globalRNorm globalSep : ℝ)
    (parent : P10SylRProblem (depth + 1))
    (child21 child11 child22 child12 : P10SylRProblem depth) where
  parent_A21_zero : p10DyadicBlock21 parent.A = 0
  parent_B21_zero : p10DyadicBlock21 parent.B = 0
  child21_A : child21.A = p10DyadicBlock22 parent.A
  child21_B : child21.B = p10DyadicBlock11 parent.B
  child21_C : child21.C = p10DyadicBlock21 parent.C
  child21_exact :
    child21.exactSolution = p10DyadicBlock21 parent.exactSolution
  child11_A : child11.A = p10DyadicBlock11 parent.A
  child11_B : child11.B = p10DyadicBlock11 parent.B
  child22_A : child22.A = p10DyadicBlock22 parent.A
  child22_B : child22.B = p10DyadicBlock22 parent.B
  child12_A : child12.A = p10DyadicBlock11 parent.A
  child12_B : child12.B = p10DyadicBlock22 parent.B
  computed_21 :
    p10DyadicBlock21 parent.computedSolution = child21.computedSolution
  computed_11 :
    p10DyadicBlock11 parent.computedSolution = child11.computedSolution
  computed_22 :
    p10DyadicBlock22 parent.computedSolution = child22.computedSolution
  computed_12 :
    p10DyadicBlock12 parent.computedSolution = child12.computedSolution
  exact_block_21 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock21 parent.exactSolution) =
      -p10DyadicBlock21 parent.C
  exact_block_11 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock11 parent.exactSolution) =
      -p10SylRExactRhs11 parent
  exact_block_22 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock22 parent.exactSolution) =
      -p10SylRExactRhs22 parent
  exact_block_12 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock12 parent.exactSolution) =
      -p10SylRExactRhs12 parent
  rhs11_first_order_error :
    p10DyadicFrobNorm (child11.C - p10SylRExactRhs11 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock11 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs22_first_order_error :
    p10DyadicFrobNorm (child22.C - p10SylRExactRhs22 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock22 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs12_first_order_error :
    p10DyadicFrobNorm (child12.C - p10SylRExactRhs12 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock12 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError11 parent child11 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock11 parent.exactSolution) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError22 parent child22 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock22 parent.exactSolution)
  assembled_error_bound :
    p10SylRForwardError parent ≤
      p10SylRBlockError21 parent child21 +
        p10SylRBlockError11 parent child11 +
        p10SylRBlockError22 parent child22 +
        p10SylRBlockError12 parent child12
  child21_first_order_error :
    p10SylRBlockError21 parent child21 ≤ smallerError
  child11_first_order_error :
    p10SylRBlockError11 parent child11 ≤
      smallerError +
        (epsilon * globalCNorm + globalANorm * smallerError +
            muHalf * epsilon * globalANorm * globalRNorm) / globalSep
  child22_first_order_error :
    p10SylRBlockError22 parent child22 ≤
      smallerError +
        (epsilon * globalCNorm + globalBNorm * smallerError +
            muHalf * epsilon * globalBNorm * globalRNorm) / globalSep
  child12_first_order_error :
    p10SylRBlockError12 parent child12 ≤
      smallerError +
        (epsilon * globalCNorm +
            (globalANorm + globalBNorm) * smallerError +
            muHalf * epsilon * (globalANorm + globalBNorm) * globalRNorm) /
          globalSep

/-- Complete proof-carrying SylR recursion family for dimensions `2^k` up to
the requested depth. `errorEnvelope k` is the attained worst first-order error
among the dimension-`2^k` calls, including rounded right-hand sides. -/
structure P10SylRRun (depth : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  mu_mono : Monotone mu
  mu_ge_one : ∀ n, 0 < n → 1 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  Node : ℕ → Type
  top : Node depth
  problem : ∀ k, k ≤ depth → Node k → P10SylRProblem k
  errorEnvelope : ℕ → ℝ
  errorEnvelope_upper : ∀ k (hk : k ≤ depth) (node : Node k),
    p10SylRForwardError (problem k hk node) ≤ errorEnvelope k
  errorEnvelope_attained : ∀ k (hk : k ≤ depth),
    ∃ node : Node k,
      p10SylRForwardError (problem k hk node) = errorEnvelope k
  child21 : ∀ k, k < depth → Node (k + 1) → Node k
  child11 : ∀ k, k < depth → Node (k + 1) → Node k
  child22 : ∀ k, k < depth → Node (k + 1) → Node k
  child12 : ∀ k, k < depth → Node (k + 1) → Node k
  level : ∀ k (hk : k < depth) (node : Node (k + 1)),
    P10SylRLevelCertificate
      epsilon (mu (2 ^ (depth - 1))) (errorEnvelope k)
      (p10DyadicFrobNorm (problem depth le_rfl top).A)
      (p10DyadicFrobNorm (problem depth le_rfl top).B)
      (p10DyadicFrobNorm (problem depth le_rfl top).C)
      (p10DyadicFrobNorm (problem depth le_rfl top).exactSolution)
      (problem depth le_rfl top).separation.value
      (problem (k + 1) (Nat.succ_le_iff.mpr hk) node)
      (problem k (Nat.le_of_lt hk) (child21 k hk node))
      (problem k (Nat.le_of_lt hk) (child11 k hk node))
      (problem k (Nat.le_of_lt hk) (child22 k hk node))
      (problem k (Nat.le_of_lt hk) (child12 k hk node))
  node_A_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).A ≤
      p10DyadicFrobNorm (problem depth le_rfl top).A
  node_B_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).B ≤
      p10DyadicFrobNorm (problem depth le_rfl top).B
  node_R_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).exactSolution ≤
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution
  node_sep_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    (problem depth le_rfl top).separation.value ≤
      (problem k hk node).separation.value
  base_rounding_bound : errorEnvelope 0 ≤
    mu (2 ^ (depth - 1)) * epsilon *
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution *
      ((p10DyadicFrobNorm (problem depth le_rfl top).A +
          p10DyadicFrobNorm (problem depth le_rfl top).B) /
        (problem depth le_rfl top).separation.value)

noncomputable def p10SylRTopProblem {depth : ℕ}
    (run : P10SylRRun depth) : P10SylRProblem depth :=
  run.problem depth le_rfl run.top

noncomputable def p10SylRConditionRatio {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  (p10DyadicFrobNorm (p10SylRTopProblem run).A +
      p10DyadicFrobNorm (p10SylRTopProblem run).B) /
    (p10SylRTopProblem run).separation.value

noncomputable def p10SylRHalfMu {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.mu (2 ^ (depth - 1))

/-- Conventional first-order forward-error scale used in the comparison
following equation (20). -/
noncomputable def p10SylRConventionalForwardScale {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon * p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    p10SylRConditionRatio run

/-- Exact multiplier in the recurrence preceding equation (20). -/
noncomputable def p10SylRRecurrenceGrowth {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  4 + 2 * p10SylRConditionRatio run

/-- Exact first-order forcing term in the recurrence preceding (20). -/
noncomputable def p10SylRRecurrenceForcing {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon / (p10SylRTopProblem run).separation.value *
    (3 * p10DyadicFrobNorm (p10SylRTopProblem run).C +
      2 * p10SylRHalfMu run *
        (p10DyadicFrobNorm (p10SylRTopProblem run).A +
          p10DyadicFrobNorm (p10SylRTopProblem run).B) *
        p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution)

/-- Equation (20) with the explicit universal constant `2`; this is a finite
strengthening of the paper's unspecified big-O constant. -/
noncomputable def p10SylREquation20Bound {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
    p10SylRHalfMu run * run.epsilon *
    p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    (p10SylRConditionRatio run) ^ (1 + Nat.log2 (2 ^ depth))

/-- Finite form of the recurrence, equation (20), its conventional-error
comparison, and the logarithmic condition-number exponent. -/
def P10SylRLogarithmicallyStable {depth : ℕ}
    (run : P10SylRRun depth) : Prop :=
  (∀ k, k < depth →
      run.errorEnvelope (k + 1) ≤
        p10SylRRecurrenceGrowth run * run.errorEnvelope k +
          p10SylRRecurrenceForcing run) ∧
    p10SylRForwardError (p10SylRTopProblem run) ≤
      p10SylREquation20Bound run ∧
    p10SylREquation20Bound run =
      2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
        p10SylRHalfMu run * p10SylRConventionalForwardScale run *
        (p10SylRConditionRatio run) ^ Nat.log2 (2 ^ depth) ∧
    1 + Nat.log2 (2 ^ depth) = depth + 1

end HighamBench
```
