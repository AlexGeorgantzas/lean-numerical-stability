# Declaration dossier for P09-T3

This dossier describes the theorem statement only. Its proof is excluded.
Judges must interpret every dependency entry and may not infer semantics from names.

## Exact source declaration

```lean
theorem p09_t3_multidimensional_rms_error_bound
    {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ)
    (family : P09AsymptoticMultidimensionalFftFamily plan γ)
    (axisBounds : P09TheoremTwoLocalAsymptotic family)
    (hexactOutput : 0 < p09MultiRms (p09FamilyMultiExactOutput family)) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ ε : P09PositiveEpsilon, ε.1 ≤ radius →
          p09MultiRms (p09FamilyMultiFftRoundoffError family ε) /
              p09MultiRms (p09FamilyMultiExactOutput family) ≤
            ε.1 * (∑ i : Fin m, p09AxisK (plan.axis i) γ) +
              secondOrderCoeff * ε.1 ^ 2
```

## Elaborated target type

```lean
∀ {m : Nat} [inst : NeZero m] (plan : HighamBench.P09MultidimensionalFftPlan m) (γ : Real)
  (family : HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ)
  (axisBounds : HighamBench.P09TheoremTwoLocalAsymptotic family),
  Real.instLT.lt 0 (HighamBench.p09MultiRms (HighamBench.p09FamilyMultiExactOutput family)) →
    Exists fun secondOrderCoeff =>
      And (Real.instLE.le 0 secondOrderCoeff)
        (Exists fun radius =>
          And (Real.instLT.lt 0 radius)
            (∀ (ε : HighamBench.P09PositiveEpsilon),
              Real.instLE.le ε.val radius →
                Real.instLE.le
                  (instHDiv.hDiv (HighamBench.p09MultiRms (HighamBench.p09FamilyMultiFftRoundoffError family ε))
                    (HighamBench.p09MultiRms (HighamBench.p09FamilyMultiExactOutput family)))
                  (instHAdd.hAdd (instHMul.hMul ε.val (Finset.univ.sum fun i => HighamBench.p09AxisK (plan.axis i) γ))
                    (instHMul.hMul secondOrderCoeff (instHPow.hPow ε.val 2)))))
```

## Fully explicit elaborated target type

```lean
∀ {m : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m]
  (plan : @HighamBench.P09MultidimensionalFftPlan m inst) (γ : Real)
  (family : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ)
  (axisBounds : @HighamBench.P09TheoremTwoLocalAsymptotic m inst plan γ family)
  (hexactOutput :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HighamBench.p09MultiRms m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
        (@HighamBench.p09FamilyMultiExactOutput m inst plan γ family))),
  @Exists.{1} Real fun (secondOrderCoeff : Real) =>
    And
      (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        secondOrderCoeff)
      (@Exists.{1} Real fun (radius : Real) =>
        And
          (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            radius)
          (∀ (ε : HighamBench.P09PositiveEpsilon),
            @LE.le.{0} Real Real.instLE
                (@Subtype.val.{1} Real
                  (fun (ε : Real) =>
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                  ε)
                radius →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HighamBench.p09MultiRms m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
                    (@HighamBench.p09FamilyMultiFftRoundoffError m inst plan γ family ε))
                  (@HighamBench.p09MultiRms m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
                    (@HighamBench.p09FamilyMultiExactOutput m inst plan γ family)))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@Subtype.val.{1} Real
                      (fun (ε : Real) =>
                        @LT.lt.{0} Real Real.instLT
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                      ε)
                    (@Finset.sum.{0, 0} (Fin m) Real Real.instAddCommMonoid (@Finset.univ.{0} (Fin m) (Fin.fintype m))
                      fun (i : Fin m) =>
                      HighamBench.p09AxisK (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan i) γ))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) secondOrderCoeff
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                      (@Subtype.val.{1} Real
                        (fun (ε : Real) =>
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                        ε)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
```

## Local import graph

- `AuditTarget` imports: `HighamBench.P09Definitions`
- `HighamBench.Core` imports: `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`
- `HighamBench.P09Base` imports: `HighamBench.Core`, `Mathlib.Algebra.Order.Chebyshev`, `Mathlib.Analysis.Fourier.ZMod`, `Mathlib.Analysis.InnerProductSpace.PiL2`
- `HighamBench.P09TheoremOne` imports: `HighamBench.P09Base`
- `HighamBench.P09Definitions` imports: `HighamBench.P09Base`, `HighamBench.P09TheoremOne`

## Semantic dependency inventory

`local` entries are recursively followed through their types and bodies. `external-frontier` entries are the exact Lean/mathlib declarations where that recursive traversal stops; their types and one-level bodies are still shown.

### D001: `HighamBench.P09AsymptoticMultidimensionalFftFamily`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `d05d5686c6b18c0c59b6d9f4ad503f21b4637b5c6696b1994b99f70f69de41c3`

Type:

```lean
{m : Nat} → [inst : NeZero m] → HighamBench.P09MultidimensionalFftPlan m → Real → Type
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    (plan : @HighamBench.P09MultidimensionalFftPlan m inst) → (γ : Real) → Type
```

### D002: `HighamBench.P09MultidimensionalFftPlan`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `58bab8e315f44effb185c1d33c722eff095b555eb7ca8dd500dbb46d9ef6e139`

Type:

```lean
(m : Nat) → [NeZero m] → Type
```

Fully explicit type:

```lean
(m : Nat) → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] → Type
```

### D003: `HighamBench.P09MultidimensionalFftPlan.axis`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `4f110c9cf1b68a953de7ce0fe7079241b2b00d4c3d894621f816d6d6fee42e66`

Type:

```lean
{m : Nat} → [inst : NeZero m] → HighamBench.P09MultidimensionalFftPlan m → Fin m → HighamBench.P09FftAxis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    (self : @HighamBench.P09MultidimensionalFftPlan m inst) → Fin m → HighamBench.P09FftAxis
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] self => self.1
```

### D004: `HighamBench.P09PositiveEpsilon`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `beaffc17a0637e2134854464050914551f29b26c09b92cbdd3d2ca9db575822a`

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
Subtype fun ε => Real.instLT.lt 0 ε
```

### D005: `HighamBench.P09TheoremTwoLocalAsymptotic`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `0c60dcd3f7eeab991738509407a3367e7ac62c71c3aa922c9cb7acfb2c85ad9e`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} → HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ → Type
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} → (family : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) → Type
```

### D006: `HighamBench.p09AxisK`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `7ae8163a8ca36c47b293ac8b68040f731a151b3d64a7bba3a80d5e2ac046c01c`

Type:

```lean
HighamBench.P09FftAxis → Real → Real
```

Fully explicit type:

```lean
(axis : HighamBench.P09FftAxis) → (γ : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun axis γ => HighamBench.p09K axis.plan γ
```

### D007: `HighamBench.p09FamilyMultiExactOutput`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `2b55efdad40a9e14c40a09c8158e5be74b52559641acc5f8623ed7307fad0aca`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} → HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (family : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) →
          @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {γ} family => HighamBench.p09ApplyCoordinatePrefix plan.axis m family.input
```

### D008: `HighamBench.p09FamilyMultiFftRoundoffError`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `3dcad2f55a16277e4401b13dbee598cdd3ad233513b81c7912cdd179e2107b23`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} →
        HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ →
          HighamBench.P09PositiveEpsilon → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (family : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) →
          (ε : HighamBench.P09PositiveEpsilon) →
            @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {γ} family ε =>
  HighamBench.p09MultiVecSub (HighamBench.p09MultiComputedOutput (family.run ε))
    (HighamBench.p09FamilyMultiExactOutput family)
```

### D009: `HighamBench.p09MultiRms`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `6eee10965db8466a35204629cd892a83cd68269afa7c165c04ad4c86d9e5e9e7`

Type:

```lean
{m : Nat} → {axis : Fin m → HighamBench.P09FftAxis} → HighamBench.P09MultiArray axis → Real
```

Fully explicit type:

```lean
{m : Nat} → {axis : Fin m → HighamBench.P09FftAxis} → (x : @HighamBench.P09MultiArray m axis) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => instHDiv.hDiv (HighamBench.p09MultiNorm2 x) (HighamBench.p09MultiCardinality axis).cast.sqrt
```

### D010: `HighamBench.P09AsymptoticMultidimensionalFftFamily.input`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `0aa258366ee6c13873f937e207223fa0b65ab3c5953b507ef0b3e0331b6c8b4c`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} → HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (self : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) →
          @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.2
```

### D011: `HighamBench.P09AsymptoticMultidimensionalFftFamily.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `423bb3c4e8aefb13eda1e6ba24d2d5389d1d853aeb42b6fad273b5e4a97a9b47`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} →
        Real.instLE.le 0 γ →
          (input : HighamBench.P09MultiArray plan.axis) →
            (model : HighamBench.P09PositiveEpsilon → HighamBench.P09WilkinsonModel) →
              (∀ (ε : HighamBench.P09PositiveEpsilon), Eq (model ε).epsilon ε.val) →
                (∀ (ε : HighamBench.P09PositiveEpsilon), Eq (model ε).gamma γ) →
                  (run : (ε : HighamBench.P09PositiveEpsilon) → HighamBench.P09MultidimensionalFftRun plan (model ε)) →
                    (∀ (ε : HighamBench.P09PositiveEpsilon), Eq (run ε).input input) →
                      HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (gamma_nonneg :
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) γ) →
          (input : @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)) →
            (model : HighamBench.P09PositiveEpsilon → HighamBench.P09WilkinsonModel) →
              (model_epsilon :
                  ∀ (ε : HighamBench.P09PositiveEpsilon),
                    @Eq.{1} Real (HighamBench.P09WilkinsonModel.epsilon (model ε))
                      (@Subtype.val.{1} Real
                        (fun (ε : Real) =>
                          @LT.lt.{0} Real Real.instLT
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                        ε)) →
                (model_gamma :
                    ∀ (ε : HighamBench.P09PositiveEpsilon),
                      @Eq.{1} Real (HighamBench.P09WilkinsonModel.gamma (model ε)) γ) →
                  (run :
                      (ε : HighamBench.P09PositiveEpsilon) →
                        @HighamBench.P09MultidimensionalFftRun m inst plan (model ε)) →
                    (run_input :
                        ∀ (ε : HighamBench.P09PositiveEpsilon),
                          @Eq.{1}
                            (@HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan))
                            (@HighamBench.P09MultidimensionalFftRun.input m inst plan (model ε) (run ε)) input) →
                      @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ
```

### D012: `HighamBench.P09AsymptoticMultidimensionalFftFamily.model`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b897022e460d5361f9607e799acbda7145c14300bc49abdb25ddcc70417b781c`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} →
        HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ →
          HighamBench.P09PositiveEpsilon → HighamBench.P09WilkinsonModel
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (self : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) →
          HighamBench.P09PositiveEpsilon → HighamBench.P09WilkinsonModel
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.3
```

### D013: `HighamBench.P09AsymptoticMultidimensionalFftFamily.run`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `93471286ff34c2ec5a540995ec567cd6b8fd9ed10e5f24d7319aa7bc677835d8`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} →
        (self : HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ) →
          (ε : HighamBench.P09PositiveEpsilon) → HighamBench.P09MultidimensionalFftRun plan (self.model ε)
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        (self : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ) →
          (ε : HighamBench.P09PositiveEpsilon) →
            @HighamBench.P09MultidimensionalFftRun m inst plan
              (@HighamBench.P09AsymptoticMultidimensionalFftFamily.model m inst plan γ self ε)
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan γ self => self.6
```

### D014: `HighamBench.P09FftAxis`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `2`
- Semantic SHA-256: `ac66534455188396047a24b2dc5dec1df9477b2eb3f74be4e03fbe9e759b3c4f`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D015: `HighamBench.P09FftAxis.order`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `9a844cefb047ec694462340588b90aa4a1eb84beb0b1a5a1e9e1ee8b02595e02`

Type:

```lean
HighamBench.P09FftAxis → Nat
```

Fully explicit type:

```lean
(self : HighamBench.P09FftAxis) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D016: `HighamBench.P09FftAxis.plan`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `b3432d3a4dcdb8a08c47c7f6290a10957c5d2a7ba05a5b33a6d76d36eb99c63b`

Type:

```lean
(self : HighamBench.P09FftAxis) → HighamBench.P09MixedRadixFftPlan self.order
```

Fully explicit type:

```lean
(self : HighamBench.P09FftAxis) →
  @HighamBench.P09MixedRadixFftPlan (HighamBench.P09FftAxis.order self)
    (@NeZero.mk.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (HighamBench.P09FftAxis.order self)
      (@Nat.ne_of_gt (HighamBench.P09FftAxis.order self)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)))
        (HighamBench.P09FftAxis.order_pos self)))
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D017: `HighamBench.P09MultiArray`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `2`
- Semantic SHA-256: `2f9ce4011814cb13d57a3f5520aeb8e5b4c5e9c6ca44b6da84ece99e718e1ac0`

Type:

```lean
{m : Nat} → (Fin m → HighamBench.P09FftAxis) → Type
```

Fully explicit type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => HighamBench.P09MultiIndex axis → Complex
```

### D018: `HighamBench.P09MultidimensionalFftPlan.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `3ed2bbd90ecca022b810ebf3044f9769f3c6330fda82583fab6398a84353607b`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    (axis : Fin m → HighamBench.P09FftAxis) →
      (∀ (k : Nat) (hk : instLENat.le k m) (x : HighamBench.P09MultiArray axis),
          Eq (HighamBench.p09MultiRms (HighamBench.p09ApplyCoordinatePrefix axis k x))
            (instHMul.hMul (HighamBench.p09PrefixOrderProduct axis k hk).cast.sqrt (HighamBench.p09MultiRms x))) →
        HighamBench.P09MultidimensionalFftPlan m
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    (axis : Fin m → HighamBench.P09FftAxis) →
      (prefix_rms_scaling :
          ∀ (k : Nat) (hk : @LE.le.{0} Nat instLENat k m) (x : @HighamBench.P09MultiArray m axis),
            @Eq.{1} Real (@HighamBench.p09MultiRms m axis (@HighamBench.p09ApplyCoordinatePrefix m axis k x))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast (@HighamBench.p09PrefixOrderProduct m axis k hk)))
                (@HighamBench.p09MultiRms m axis x))) →
        @HighamBench.P09MultidimensionalFftPlan m inst
```

### D019: `HighamBench.P09TheoremTwoLocalAsymptotic.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `2`
- Semantic SHA-256: `58cf28bc10bdf6961ba67f2133e5ff898982872d1214b6871dbb3dfeae8c4822`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {γ : Real} →
        {family : HighamBench.P09AsymptoticMultidimensionalFftFamily plan γ} →
          (localSecondOrderCoeff : Fin m → Real) →
            (∀ (i : Fin m), Real.instLE.le 0 (localSecondOrderCoeff i)) →
              (radius : Real) →
                Real.instLT.lt 0 radius →
                  (∀ (ε : HighamBench.P09PositiveEpsilon),
                      Real.instLE.le ε.val radius →
                        ∀ (i : Fin m),
                          Real.instLE.le (HighamBench.p09MultiRms (HighamBench.p09PropagatedAxisError (family.run ε) i))
                            (instHAdd.hAdd
                              (instHMul.hMul (instHMul.hMul ε.val (HighamBench.p09AxisK (plan.axis i) γ))
                                (HighamBench.p09PropagatedStageInputRms (family.run ε) i))
                              (instHMul.hMul (localSecondOrderCoeff i) (instHPow.hPow ε.val 2)))) →
                    HighamBench.P09TheoremTwoLocalAsymptotic family
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {γ : Real} →
        {family : @HighamBench.P09AsymptoticMultidimensionalFftFamily m inst plan γ} →
          (localSecondOrderCoeff : Fin m → Real) →
            (local_second_order_nonneg :
                ∀ (i : Fin m),
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (localSecondOrderCoeff i)) →
              (radius : Real) →
                (radius_pos :
                    @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) radius) →
                  (local_error_bound :
                      ∀ (ε : HighamBench.P09PositiveEpsilon),
                        @LE.le.{0} Real Real.instLE
                            (@Subtype.val.{1} Real
                              (fun (ε : Real) =>
                                @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                              ε)
                            radius →
                          ∀ (i : Fin m),
                            @LE.le.{0} Real Real.instLE
                              (@HighamBench.p09MultiRms m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
                                (@HighamBench.p09PropagatedAxisError m inst plan
                                  (@HighamBench.P09AsymptoticMultidimensionalFftFamily.model m inst plan γ family ε)
                                  (@HighamBench.P09AsymptoticMultidimensionalFftFamily.run m inst plan γ family ε) i))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@Subtype.val.{1} Real
                                      (fun (ε : Real) =>
                                        @LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                                      ε)
                                    (HighamBench.p09AxisK (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan i)
                                      γ))
                                  (@HighamBench.p09PropagatedStageInputRms m inst plan
                                    (@HighamBench.P09AsymptoticMultidimensionalFftFamily.model m inst plan γ family ε)
                                    (@HighamBench.P09AsymptoticMultidimensionalFftFamily.run m inst plan γ family ε) i))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (localSecondOrderCoeff i)
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat (@Monoid.toNatPow.{0} Real Real.instMonoid))
                                    (@Subtype.val.{1} Real
                                      (fun (ε : Real) =>
                                        @LT.lt.{0} Real Real.instLT
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε)
                                      ε)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                    @HighamBench.P09TheoremTwoLocalAsymptotic m inst plan γ family
```

### D020: `HighamBench.p09ApplyCoordinatePrefix`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd827baff3bc1c82b878f4ab9412f49737659b6ba14c6339c01d09b26ae23f56`

Type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) → Nat → HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis
```

Fully explicit type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) → Nat → @HighamBench.P09MultiArray m axis → @HighamBench.P09MultiArray m axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis x x_1 =>
  Nat.brecOn (motive := fun x => HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis) x
    (fun x f x_2 =>
      HighamBench.p09ApplyCoordinatePrefix.match_1 axis
        (fun x x_3 =>
          Nat.below (motive := fun x => HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis) x →
            HighamBench.P09MultiArray axis)
        x x_2 (fun x x_3 => x) (fun i x x_3 => x_3.1 (HighamBench.p09CoordinateTransformNat axis i x)) f)
    x_1
```

### D021: `HighamBench.p09AxisK._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `2`
- Semantic SHA-256: `edf8eb530e4de69022d7e6aba03bd4f4a8892d564b0a25aea87576d7ce058e2b`

Type:

```lean
∀ (axis : HighamBench.P09FftAxis), NeZero axis.order
```

Fully explicit type:

```lean
∀ (axis : HighamBench.P09FftAxis),
  @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (HighamBench.P09FftAxis.order axis)
```

### D022: `HighamBench.p09K`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `dd675c229b9fa903ef8bc454abb7ca04d584da2f71399f32f0893ab66e78aeb4`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixFftPlan n → Real → Real
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (plan : @HighamBench.P09MixedRadixFftPlan n inst) → (γ : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] plan γ =>
  instHAdd.hAdd (Finset.univ.sum fun i => HighamBench.p09Alpha (plan.stage i).radix γ)
    (instHMul.hMul (instHSub.hSub plan.stageCount.cast 1) (instHAdd.hAdd 3 (instHMul.hMul 2 γ)))
```

### D023: `HighamBench.p09MultiCardinality`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `c6f5ee16e064cc48c4b30549e7081a27fc5cb52dfaf0efe4b55c47f65cbd2916`

Type:

```lean
{m : Nat} → (Fin m → HighamBench.P09FftAxis) → Nat
```

Fully explicit type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => Finset.univ.prod fun i => (axis i).order
```

### D024: `HighamBench.p09MultiComputedOutput`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `f5a5a454db23d56a07eb881bbafbff8dd4ac1648d00e40ed0a8179233ff78543`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        HighamBench.P09MultidimensionalFftRun plan model → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (run : @HighamBench.P09MultidimensionalFftRun m inst plan model) →
          @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run => run.computedState 0
```

### D025: `HighamBench.p09MultiNorm2`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `a2959c76d4fcecf46d1d1c3d6b3cf0f954d9bd8c73d5cb3f35b4ef1173797a5d`

Type:

```lean
{m : Nat} → {axis : Fin m → HighamBench.P09FftAxis} → HighamBench.P09MultiArray axis → Real
```

Fully explicit type:

```lean
{m : Nat} → {axis : Fin m → HighamBench.P09FftAxis} → (x : @HighamBench.P09MultiArray m axis) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x => (PiLp.instNorm 2 fun x => Complex).norm { ofLp := x }
```

### D026: `HighamBench.p09MultiVecSub`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `2`
- Semantic SHA-256: `17a2e90cf50d4a2223edb4a0ac0dac08bc748ae303ecd2570d356d2a134085d6`

Type:

```lean
{m : Nat} →
  {axis : Fin m → HighamBench.P09FftAxis} →
    HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis
```

Fully explicit type:

```lean
{m : Nat} →
  {axis : Fin m → HighamBench.P09FftAxis} →
    (x y : @HighamBench.P09MultiArray m axis) → @HighamBench.P09MultiArray m axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} {axis} x y index => instHSub.hSub (x index) (y index)
```

### D027: `HighamBench.P09FftAxis.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e6932f525aaf103773642eaa6ac58f458c33c4a28215567401e60c1a14d1e63f`

Type:

```lean
(order : Nat) → (order_pos : instLTNat.lt 0 order) → HighamBench.P09MixedRadixFftPlan order → HighamBench.P09FftAxis
```

Fully explicit type:

```lean
(order : Nat) →
  (order_pos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) order) →
    (plan :
        @HighamBench.P09MixedRadixFftPlan order
          (@NeZero.mk.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) order
            (@Nat.ne_of_gt order
              (@OfNat.ofNat.{0} Nat (nat_lit 0)
                (@Zero.toOfNat0.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)))
              order_pos))) →
      HighamBench.P09FftAxis
```

### D028: `HighamBench.P09FftAxis.order_pos`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `cd325b50a3f2d950540c358bf3d3fe994ea81ae59412face1a635bd048549ad1`

Type:

```lean
∀ (self : HighamBench.P09FftAxis), instLTNat.lt 0 self.order
```

Fully explicit type:

```lean
∀ (self : HighamBench.P09FftAxis),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (HighamBench.P09FftAxis.order self)
```

### D029: `HighamBench.P09MixedRadixFftPlan`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `773b59c0343db6824933ffd9eaca8956809e69ed57df9d1df00ca0a512fd9cf9`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

Fully explicit type:

```lean
(n : Nat) → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → Type
```

### D030: `HighamBench.P09MixedRadixFftPlan.stage`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `26bdd691cae4e7dccd873b3d4e2f8e6acc0d579b4b693a56cda8b84cf81f647a`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : HighamBench.P09MixedRadixFftPlan n) → Fin self.stageCount → HighamBench.P09MixedRadixStage n
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixFftPlan n inst) →
      Fin (@HighamBench.P09MixedRadixFftPlan.stageCount n inst self) → @HighamBench.P09MixedRadixStage n inst
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.3
```

### D031: `HighamBench.P09MixedRadixFftPlan.stageCount`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `30ab40fa47995b63b1565b7425deadb31034b8e5eb50c4ce28fcbf1f41a4724b`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixFftPlan n → Nat
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixFftPlan n inst) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D032: `HighamBench.P09MixedRadixStage.radix`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `468911f06d3c718429ca65245988f62b98377f7d7648153228b930bbe9358eef`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → Nat
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.1
```

### D033: `HighamBench.P09MultiIndex`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `d973f8a39a59e78c19aa706841d53c945249d626875d1297c105d303dad1fb68`

Type:

```lean
{m : Nat} → (Fin m → HighamBench.P09FftAxis) → Type
```

Fully explicit type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → Type
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => (i : Fin m) → ZMod (axis i).order
```

### D034: `HighamBench.P09MultidimensionalFftRun`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `876c6afa53aa36168b61e5b894e88a15ff2c6961bf2a6d30155b0102ec51263a`

Type:

```lean
{m : Nat} → [inst : NeZero m] → HighamBench.P09MultidimensionalFftPlan m → HighamBench.P09WilkinsonModel → Type
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    (plan : @HighamBench.P09MultidimensionalFftPlan m inst) → (model : HighamBench.P09WilkinsonModel) → Type
```

### D035: `HighamBench.P09MultidimensionalFftRun.computedState`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `c3374523bbfbc42ab75c69ecd351f84e9abfde35fe203c838a1b06708d10c243`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        HighamBench.P09MultidimensionalFftRun plan model → Fin (instHAdd.hAdd m 1) → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (self : @HighamBench.P09MultidimensionalFftRun m inst plan model) →
          Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.2
```

### D036: `HighamBench.P09MultidimensionalFftRun.input`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `f55929524fb5c391c159443dbdb100a8bdbe998fe0ad5b0ed4c51d3335adb68a`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        HighamBench.P09MultidimensionalFftRun plan model → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (self : @HighamBench.P09MultidimensionalFftRun m inst plan model) →
          @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun m [NeZero m] plan model self => self.1
```

### D037: `HighamBench.P09WilkinsonModel`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `c7339f4ea02dd9cfdae11d3d03937bb79376d62f6d50b4bd3b3a857c02fe2728`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D038: `HighamBench.P09WilkinsonModel.epsilon`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `710e3ebacedae5bde70ccdf11768df1bab629b60ff87cf70e8ab4f5e14f3d687`

Type:

```lean
HighamBench.P09WilkinsonModel → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D039: `HighamBench.P09WilkinsonModel.gamma`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `338fc4d07b6457fb813e32f105b95cb112e42125bdf72f24736d6b0e4956d063`

Type:

```lean
HighamBench.P09WilkinsonModel → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.3
```

### D040: `HighamBench.p09Alpha`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `c606d19a89a02456d06023ca3fdcae9710ad57298e71db6ef1dcda9da539074d`

Type:

```lean
Nat → Real → Real
```

Fully explicit type:

```lean
(q : Nat) → (γ : Real) → Real
```

Definition body (one-level semantic boundary):

```lean
fun q γ =>
  ite (Eq q 2) (Real.sqrt 2) (ite (Eq q 4) 5 (instHMul.hMul (instHMul.hMul 2 q.cast.sqrt) (instHAdd.hAdd q.cast γ)))
```

### D041: `HighamBench.p09Alpha._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `dfed3ec56d4bb1b4d13cb4e24bd15dcacdbd2f1f8f2e4c150658454e768ae9a9`

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

### D042: `HighamBench.p09ApplyCoordinatePrefix.match_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `236ac002bf53dca67fe09fbec8832569ac4c1b3a6ea4221a7ad4f57b906fb6ec`

Type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    (motive : Nat → HighamBench.P09MultiArray axis → Sort u_1) →
      (x : Nat) →
        (x_1 : HighamBench.P09MultiArray axis) →
          ((x : HighamBench.P09MultiArray axis) → motive 0 x) →
            ((i : Nat) → (x : HighamBench.P09MultiArray axis) → motive i.succ x) → motive x x_1
```

Fully explicit type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    (motive : Nat → @HighamBench.P09MultiArray m axis → Sort u_1) →
      (x : Nat) →
        (x_1 : @HighamBench.P09MultiArray m axis) →
          (h_1 :
              (x : @HighamBench.P09MultiArray m axis) →
                motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x) →
            (h_2 : (i : Nat) → (x : @HighamBench.P09MultiArray m axis) → motive (Nat.succ i) x) → motive x x_1
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis motive x x_1 h_1 h_2 => Nat.casesOn x (h_1 x_1) fun n => h_2 n x_1
```

### D043: `HighamBench.p09CoordinateTransformNat`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `7ebe006704510fd5a6e39f79fbc1455373aa630b151bffe2b2ffa099992c53fe`

Type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) → Nat → HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis
```

Fully explicit type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    (i : Nat) → (x : @HighamBench.P09MultiArray m axis) → @HighamBench.P09MultiArray m axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x => if hi : instLTNat.lt i m then HighamBench.p09CoordinateTransform axis ⟨i, hi⟩ x else x
```

### D044: `HighamBench.p09K._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `adfe6af1174d8fcac0c7a06078c0cdb374594faed75a449c3fa4a00bc0242be0`

Type:

```lean
(instHAdd.hAdd 2 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D045: `HighamBench.p09MultiComputedOutput._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `aeb0224e18190851754ceb4dad01f755e356b698ee50f14799402dbe28c3c13a`

Type:

```lean
∀ {m : Nat}, NeZero (instHAdd.hAdd m 1)
```

Fully explicit type:

```lean
∀ {m : Nat},
  @NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D046: `HighamBench.p09MultiIndexFintype`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `4d533a705d545f677469b8b56e5c398d8c65bbf78bdc6a5625f087fe003f10f3`

Type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → Fintype (HighamBench.P09MultiIndex axis)
```

Fully explicit type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → Fintype.{0} (@HighamBench.P09MultiIndex m axis)
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis => inferInstance
```

### D047: `HighamBench.p09PrefixOrderProduct`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `9f8907da618e1cfdb879834cb3fd959ccea5f7a359a6389b068f26476ef4387f`

Type:

```lean
{m : Nat} → (Fin m → HighamBench.P09FftAxis) → (k : Nat) → instLENat.le k m → Nat
```

Fully explicit type:

```lean
{m : Nat} → (axis : Fin m → HighamBench.P09FftAxis) → (k : Nat) → (hk : @LE.le.{0} Nat instLENat k m) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis k hk => Finset.univ.prod fun i => (axis (Fin.castLE hk i)).order
```

### D048: `HighamBench.p09PropagatedAxisError`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a4d7c6586c8dfee1f8ecfd638208c4f41357952c9ee5bdda04404e3a7917df45`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        HighamBench.P09MultidimensionalFftRun plan model → Fin m → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (run : @HighamBench.P09MultidimensionalFftRun m inst plan model) →
          (i : Fin m) → @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  HighamBench.p09ApplyCoordinatePrefix plan.axis i.val (HighamBench.p09AxisLocalError run i)
```

### D049: `HighamBench.p09PropagatedStageInputRms`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `a67da1427a25e222d9393e4671544366a435b5467b20170e98f7ca088968035e`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} → HighamBench.P09MultidimensionalFftRun plan model → Fin m → Real
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (run : @HighamBench.P09MultidimensionalFftRun m inst plan model) → (i : Fin m) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  HighamBench.p09MultiRms
    (HighamBench.p09ApplyCoordinatePrefix plan.axis (instHAdd.hAdd i.val 1) (run.computedState i.succ))
```

### D050: `HighamBench.P09MixedRadixFftPlan.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `34e16979d88f342f79a1e32d13ffce39b5eefa5cc935f4bdf81abe3a748c8518`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (stageCount : Nat) →
      instLTNat.lt 0 stageCount →
        (stage : Fin stageCount → HighamBench.P09MixedRadixStage n) →
          Eq (Finset.univ.prod fun i => (stage i).radix) n →
            (∀ (i : Fin stageCount),
                Eq (stage i).useTwiddle (Decidable.decide (instLTNat.lt (instHAdd.hAdd i.val 1) stageCount))) →
              (finalPermutation : Equiv (ZMod n) (ZMod n)) →
                HighamBench.P09FftVariant →
                  (∀ (x : ZMod n → Complex),
                      Eq (HighamBench.p09Permute finalPermutation (HighamBench.p09ApplyMixedRadixStages stage x))
                        (HighamBench.p09FourierTransform x)) →
                    (∀ (i : Fin stageCount) (x : ZMod n → Complex),
                        Eq (HighamBench.p09ComplexNorm2 (HighamBench.p09MixedRadixStageApply (stage i) x))
                          (instHMul.hMul (stage i).radix.cast.sqrt (HighamBench.p09ComplexNorm2 x))) →
                      Function.Surjective HighamBench.p09FourierTransform →
                        (∀ (x : ZMod n → Complex),
                            Eq (HighamBench.p09ComplexRms (HighamBench.p09FourierTransform x))
                              (instHMul.hMul n.cast.sqrt (HighamBench.p09ComplexRms x))) →
                          HighamBench.P09MixedRadixFftPlan n
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (stageCount : Nat) →
      (stageCount_pos :
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) stageCount) →
        (stage : Fin stageCount → @HighamBench.P09MixedRadixStage n inst) →
          (order_factorization :
              @Eq.{1} Nat
                (@Finset.prod.{0, 0} (Fin stageCount) Nat Nat.instCommMonoid
                  (@Finset.univ.{0} (Fin stageCount) (Fin.fintype stageCount)) fun (i : Fin stageCount) =>
                  @HighamBench.P09MixedRadixStage.radix n inst (stage i))
                n) →
            (twiddle_pattern :
                ∀ (i : Fin stageCount),
                  @Eq.{1} Bool (@HighamBench.P09MixedRadixStage.useTwiddle n inst (stage i))
                    (@Decidable.decide
                      (@LT.lt.{0} Nat instLTNat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val stageCount i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        stageCount)
                      (Nat.decLt
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val stageCount i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        stageCount))) →
              (finalPermutation : Equiv.{1, 1} (ZMod n) (ZMod n)) →
                (variant : HighamBench.P09FftVariant) →
                  (exact_factorization :
                      ∀ (x : ZMod n → Complex),
                        @Eq.{1} (ZMod n → Complex)
                          (@HighamBench.p09Permute n finalPermutation
                            (@HighamBench.p09ApplyMixedRadixStages stageCount n inst stage x))
                          (@HighamBench.p09FourierTransform n inst x)) →
                    (stage_norm_scaling :
                        ∀ (i : Fin stageCount) (x : ZMod n → Complex),
                          @Eq.{1} Real
                            (@HighamBench.p09ComplexNorm2 n inst
                              (@HighamBench.p09MixedRadixStageApply n inst (stage i) x))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (Real.sqrt
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (@HighamBench.P09MixedRadixStage.radix n inst (stage i))))
                              (@HighamBench.p09ComplexNorm2 n inst x))) →
                      (fourier_surjective :
                          @Function.Surjective.{1, 1} (ZMod n → Complex) (ZMod n → Complex)
                            (@HighamBench.p09FourierTransform n inst)) →
                        (fourier_rms_scaling :
                            ∀ (x : ZMod n → Complex),
                              @Eq.{1} Real
                                (@HighamBench.p09ComplexRms n inst (@HighamBench.p09FourierTransform n inst x))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (Real.sqrt (@Nat.cast.{0} Real Real.instNatCast n))
                                  (@HighamBench.p09ComplexRms n inst x))) →
                          @HighamBench.P09MixedRadixFftPlan n inst
```

### D051: `HighamBench.P09MixedRadixStage`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `7db4d24a4acc7ed2a675a4b7ac6333f725f46008050b8ecb78e389911139f171`

Type:

```lean
(n : Nat) → [NeZero n] → Type
```

Fully explicit type:

```lean
(n : Nat) → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → Type
```

### D052: `HighamBench.P09MultidimensionalFftRun.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `e094f0859a1c82456fe5b679b9118e3d903f96148581f63caf87c12add36db72`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        (input : HighamBench.P09MultiArray plan.axis) →
          (computedState : Fin (instHAdd.hAdd m 1) → HighamBench.P09MultiArray plan.axis) →
            (∀ (index : HighamBench.P09MultiIndex plan.axis), Eq (model.flInput (input index)) (input index)) →
              Eq (computedState (Fin.last m)) input →
                (∀ (i : Fin m),
                    Eq (computedState i.castSucc)
                      (HighamBench.p09RoundedCoordinateTransform plan.axis i model (computedState i.succ))) →
                  HighamBench.P09MultidimensionalFftRun plan model
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (input : @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)) →
          (computedState :
              Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)) →
            (input_exact :
                ∀ (index : @HighamBench.P09MultiIndex m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)),
                  @Eq.{1} Complex (HighamBench.P09WilkinsonModel.flInput model (input index)) (input index)) →
              (computed_input :
                  @Eq.{1} (@HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan))
                    (computedState (Fin.last m)) input) →
                (stage_step :
                    ∀ (i : Fin m),
                      @Eq.{1} (@HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan))
                        (computedState (@Fin.castSucc m i))
                        (@HighamBench.p09RoundedCoordinateTransform m
                          (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan) i model
                          (computedState (@Fin.succ m i)))) →
                  @HighamBench.P09MultidimensionalFftRun m inst plan model
```

### D053: `HighamBench.P09WilkinsonModel.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `4`
- Semantic SHA-256: `fbf9703bb59c24f543db5a49c4099b6bc0829fd4dc51d251836ecd542f4e9c43`

Type:

```lean
(epsilon : Real) →
  Real.instLT.lt 0 epsilon →
    (gamma : Real) →
      Real.instLE.le 0 gamma →
        (flAdd flMul : Real → Real → Real) →
          (flSin flCos : Real → Real) →
            (Complex → Complex) →
              (∀ (a b : Real),
                  Exists fun θa =>
                    Exists fun θb =>
                      And (Real.instLE.le (abs θa) 1)
                        (And (Real.instLE.le (abs θb) 1)
                          (Eq (flAdd a b)
                            (instHAdd.hAdd (instHMul.hMul a (instHAdd.hAdd 1 (instHMul.hMul θa epsilon)))
                              (instHMul.hMul b (instHAdd.hAdd 1 (instHMul.hMul θb epsilon))))))) →
                (∀ (a b : Real),
                    Exists fun θ =>
                      And (Real.instLE.le (abs θ) 1)
                        (Eq (flMul a b)
                          (instHMul.hMul (instHMul.hMul a b) (instHAdd.hAdd 1 (instHMul.hMul θ epsilon))))) →
                  (∀ (a : Real),
                      Exists fun θ =>
                        And (Real.instLE.le (abs θ) 1)
                          (Eq (flSin a) (instHAdd.hAdd (Real.sin a) (instHMul.hMul (instHMul.hMul gamma θ) epsilon)))) →
                    (∀ (a : Real),
                        Exists fun θ =>
                          And (Real.instLE.le (abs θ) 1)
                            (Eq (flCos a)
                              (instHAdd.hAdd (Real.cos a) (instHMul.hMul (instHMul.hMul gamma θ) epsilon)))) →
                      HighamBench.P09WilkinsonModel
```

Fully explicit type:

```lean
(epsilon : Real) →
  (epsilon_pos :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon) →
    (gamma : Real) →
      (gamma_nonneg :
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            gamma) →
        (flAdd flMul : Real → Real → Real) →
          (flSin flCos : Real → Real) →
            (flInput : Complex → Complex) →
              (add_model :
                  ∀ (a b : Real),
                    @Exists.{1} Real fun (θa : Real) =>
                      @Exists.{1} Real fun (θb : Real) =>
                        And
                          (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θa)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (And
                            (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θb)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (@Eq.{1} Real (flAdd a b)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) θa epsilon)))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) θb
                                      epsilon))))))) →
                (mul_model :
                    ∀ (a b : Real),
                      @Exists.{1} Real fun (θ : Real) =>
                        And
                          (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θ)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (@Eq.{1} Real (flMul a b)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a b)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) θ epsilon))))) →
                  (sin_model :
                      ∀ (a : Real),
                        @Exists.{1} Real fun (θ : Real) =>
                          And
                            (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θ)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                            (@Eq.{1} Real (flSin a)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (Real.sin a)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma θ)
                                  epsilon)))) →
                    (cos_model :
                        ∀ (a : Real),
                          @Exists.{1} Real fun (θ : Real) =>
                            And
                              (@LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup θ)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                              (@Eq.{1} Real (flCos a)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (Real.cos a)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) gamma θ)
                                    epsilon)))) →
                      HighamBench.P09WilkinsonModel
```

### D054: `HighamBench.p09Alpha._proof_2`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `a49a053354e6010807fe6ee370374aca279d3828d50cd5f5908d72c6f4ed06a3`

Type:

```lean
(instHAdd.hAdd 4 1).AtLeastTwo
```

Fully explicit type:

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D055: `HighamBench.p09AxisLocalError`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `9e9e6e9c6255b7f6f4d482b4b5daf2d90579b5786356f5d6d81322fd38e56422`

Type:

```lean
{m : Nat} →
  [inst : NeZero m] →
    {plan : HighamBench.P09MultidimensionalFftPlan m} →
      {model : HighamBench.P09WilkinsonModel} →
        HighamBench.P09MultidimensionalFftRun plan model → Fin m → HighamBench.P09MultiArray plan.axis
```

Fully explicit type:

```lean
{m : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) m] →
    {plan : @HighamBench.P09MultidimensionalFftPlan m inst} →
      {model : HighamBench.P09WilkinsonModel} →
        (run : @HighamBench.P09MultidimensionalFftRun m inst plan model) →
          (i : Fin m) → @HighamBench.P09MultiArray m (@HighamBench.P09MultidimensionalFftPlan.axis m inst plan)
```

Definition body (one-level semantic boundary):

```lean
fun {m} [NeZero m] {plan} {model} run i =>
  HighamBench.p09MultiVecSub (run.computedState i.castSucc)
    (HighamBench.p09CoordinateTransform plan.axis i (run.computedState i.succ))
```

### D056: `HighamBench.p09CoordinateTransform`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7ba3c0d95e5c24277ec95ceb2d7eeb781484864eed4c154d5a12b2f1fa8b7e25`

Type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) → Fin m → HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis
```

Fully explicit type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    (i : Fin m) → (x : @HighamBench.P09MultiArray m axis) → @HighamBench.P09MultiArray m axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i x index =>
  Finset.univ.sum fun j =>
    instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j (index i))) (x (Function.update index i j))
```

### D057: `HighamBench.p09MultiIndexFintype._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `4`
- Semantic SHA-256: `ab841cfc9afa94a9c33b1bfd5aea2a395b3d437752e6903c3c10f5411ef6a8ec`

Type:

```lean
∀ {m : Nat} (axis : Fin m → HighamBench.P09FftAxis) (a : Fin m), NeZero (axis a).order
```

Fully explicit type:

```lean
∀ {m : Nat} (axis : Fin m → HighamBench.P09FftAxis) (a : Fin m),
  @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (HighamBench.P09FftAxis.order (axis a))
```

### D058: `HighamBench.P09FftVariant`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `00d481946537c4fea333af6b2e5b65d071fbe7e907bbbee20d147b733b0b9f50`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D059: `HighamBench.P09MixedRadixStage.mk`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `5`
- Semantic SHA-256: `9132ee0d9cb2aa39e88d4af0cc60ba538983d2e5aefa2c4715bd5f834ce48b55`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (radix : Nat) →
      instLENat.le 2 radix →
        Ne radix 0 →
          (blockCount : Nat) →
            Ne blockCount 0 →
              Eq (instHMul.hMul blockCount radix) n →
                Equiv (Prod (Fin blockCount) (ZMod radix)) (ZMod n) →
                  Equiv (ZMod n) (ZMod n) → Bool → (ZMod n → ZMod n) → HighamBench.P09MixedRadixStage n
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (radix : Nat) →
      (radix_two_le : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) radix) →
        (radix_ne_zero : @Ne.{1} Nat radix (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          (blockCount : Nat) →
            (blockCount_ne_zero :
                @Ne.{1} Nat blockCount (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              (order_eq :
                  @Eq.{1} Nat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) blockCount radix) n) →
                (reindex : Equiv.{1, 1} (Prod.{0, 0} (Fin blockCount) (ZMod radix)) (ZMod n)) →
                  (permutation : Equiv.{1, 1} (ZMod n) (ZMod n)) →
                    (useTwiddle : Bool) → (twiddleExponent : ZMod n → ZMod n) → @HighamBench.P09MixedRadixStage n inst
```

### D060: `HighamBench.P09MixedRadixStage.useTwiddle`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1c5c0019e9f1cde8c7ac36370ddc8cdebbeef1a81a642ea476ab75b2cfd3855c`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → Bool
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) → Bool
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.9
```

### D061: `HighamBench.P09WilkinsonModel.flInput`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `9a5ebbb64249a44b7a954dbf328f49cd90bbb1f589b9891fda13f6d5dc8bbda5`

Type:

```lean
HighamBench.P09WilkinsonModel → Complex → Complex
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Complex → Complex
```

Definition body (one-level semantic boundary):

```lean
fun self => self.9
```

### D062: `HighamBench.p09ApplyMixedRadixStages`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `765c400b21cdd5ebd4eda63b0bf2cd66d4559673516080c4beec6ca1884ea150`

Type:

```lean
{m n : Nat} → [inst : NeZero n] → (Fin m → HighamBench.P09MixedRadixStage n) → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{m n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (stages : Fin m → @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {m n} [NeZero n] stages x =>
  List.foldl (fun state stage => HighamBench.p09MixedRadixStageApply stage state) x (List.ofFn stages)
```

### D063: `HighamBench.p09ComplexNorm2`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1b98349bc6407b2f00f761222365b650c3157ff135156ae9582fc23f948737bb`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → (x : ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => (HighamBench.p09ComplexNorm2Sq x).sqrt
```

### D064: `HighamBench.p09ComplexRms`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ab12e4415ded7a43ca3c2aba733bb60da55eca72620cd80c899857c0786bafd2`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → (x : ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => instHDiv.hDiv (HighamBench.p09ComplexNorm2 x) n.cast.sqrt
```

### D065: `HighamBench.p09FourierTransform`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `88d78104400162e8766a0713158d8cf258316a0f69c768050657e6632bddd684`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x k =>
  Finset.univ.sum fun j => instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j k)) (x j)
```

### D066: `HighamBench.p09MixedRadixStageApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `451e74e88f204ff5856b21932954b13f649b07b4827c68d7994a1ad116c87c27`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x => HighamBench.p09MixedRadixTwiddleApply stage (HighamBench.p09MixedRadixBlockApply stage x)
```

### D067: `HighamBench.p09Permute`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `96b069ab581638e91c1d2748efd443ee2a1f60418baa3c54d1b78e70f25550f7`

Type:

```lean
{n : Nat} → Equiv (ZMod n) (ZMod n) → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} → (permutation : Equiv.{1, 1} (ZMod n) (ZMod n)) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} permutation x i => x (EquivLike.toFunLike.coe permutation i)
```

### D068: `HighamBench.p09RoundedCoordinateTransform`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `8d3e965aacbd8bb2f53ab4a12873c4523b9afb736ab1786c98a1cf30ba8d4a7e`

Type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    Fin m → HighamBench.P09WilkinsonModel → HighamBench.P09MultiArray axis → HighamBench.P09MultiArray axis
```

Fully explicit type:

```lean
{m : Nat} →
  (axis : Fin m → HighamBench.P09FftAxis) →
    (i : Fin m) →
      (model : HighamBench.P09WilkinsonModel) →
        (x : @HighamBench.P09MultiArray m axis) → @HighamBench.P09MultiArray m axis
```

Definition body (one-level semantic boundary):

```lean
fun {m} axis i model x index =>
  HighamBench.p09RoundedFftApply (axis i).plan model (fun j => x (Function.update index i j)) (index i)
```

### D069: `HighamBench.P09FftVariant.cooleyTukey`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `10e785826afb9f3b9b06f0132254cc389950ae6ad8ab4d338c258968f45e6420`

Type:

```lean
HighamBench.P09FftVariant
```

Fully explicit type:

```lean
HighamBench.P09FftVariant
```

### D070: `HighamBench.P09FftVariant.sandeTukey`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `constructor`
- Distance from target type: `6`
- Semantic SHA-256: `ba5af2995f3bde82b73a181429dc05616b98163594ca8b5f61325d8b159e86ff`

Type:

```lean
HighamBench.P09FftVariant
```

Fully explicit type:

```lean
HighamBench.P09FftVariant
```

### D071: `HighamBench.p09ComplexNorm2Sq`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `d588903d42ed5e62a89abc9383bb26b4dda08d79d6524663ff72c7d012ba072f`

Type:

```lean
{n : Nat} → [NeZero n] → (ZMod n → Complex) → Real
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → (x : ZMod n → Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] x => Finset.univ.sum fun i => instHPow.hPow (Complex.instNorm.norm (x i)) 2
```

### D072: `HighamBench.p09MixedRadixBlockApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `ff5733b14f40eec996881be82ff09fea976cd958c7cb474a0cea8c8c6b1a8931`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x =>
  have permuted := fun i => x (EquivLike.toFunLike.coe stage.permutation i);
  fun i =>
  have bi := EquivLike.toFunLike.coe stage.reindex.symm i;
  Finset.univ.sum fun j =>
    instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (instHMul.hMul j bi.snd))
      (permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := j }))
```

### D073: `HighamBench.p09MixedRadixTwiddleApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `74e893bbbec094924bb26744b622fd11831b889d775381fddb4055302329d855`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] stage x i =>
  ite (Eq stage.useTwiddle Bool.true)
    (instHMul.hMul (AddChar.instFunLike.coe ZMod.stdAddChar (stage.twiddleExponent i)) (x i)) (x i)
```

### D074: `HighamBench.p09RoundedFftApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `9b7d3ed0d2368b6ce3d657f70e4e8152625997f2f49617ef723841f6e22bc970`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    HighamBench.P09MixedRadixFftPlan n → HighamBench.P09WilkinsonModel → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (plan : @HighamBench.P09MixedRadixFftPlan n inst) →
      (model : HighamBench.P09WilkinsonModel) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] plan model x =>
  HighamBench.p09Permute plan.finalPermutation (HighamBench.p09ApplyRoundedMixedRadixStages model plan.stage x)
```

### D075: `HighamBench.P09MixedRadixFftPlan.finalPermutation`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `d1331890684f080fcbb319c8fe62402503a57488940282cabe28c1c237f81342`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixFftPlan n → Equiv (ZMod n) (ZMod n)
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixFftPlan n inst) → Equiv.{1, 1} (ZMod n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.6
```

### D076: `HighamBench.P09MixedRadixStage.blockCount`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `545e215ef4fcce115250d537eaa2cb06c5cb57dc5bd5b39d6f1cbe9a48630828`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → Nat
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) → Nat
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.4
```

### D077: `HighamBench.P09MixedRadixStage.permutation`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `965e6f08ad6f204c13157a8fe9e1a155901194e09609769a0f659421aa651e78`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → Equiv (ZMod n) (ZMod n)
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) → Equiv.{1, 1} (ZMod n) (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.8
```

### D078: `HighamBench.P09MixedRadixStage.reindex`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `dec33918992898801b2323263f5c4a02b324c3fcb105fec185c31497783e37bf`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    (self : HighamBench.P09MixedRadixStage n) → Equiv (Prod (Fin self.blockCount) (ZMod self.radix)) (ZMod n)
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) →
      Equiv.{1, 1}
        (Prod.{0, 0} (Fin (@HighamBench.P09MixedRadixStage.blockCount n inst self))
          (ZMod (@HighamBench.P09MixedRadixStage.radix n inst self)))
        (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.7
```

### D079: `HighamBench.P09MixedRadixStage.twiddleExponent`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `caf272fc6b71ebb3ae0eeb0ce6ab014ea8e189e658f1ebee865503f36400857f`

Type:

```lean
{n : Nat} → [inst : NeZero n] → HighamBench.P09MixedRadixStage n → ZMod n → ZMod n
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (self : @HighamBench.P09MixedRadixStage n inst) → ZMod n → ZMod n
```

Definition body (one-level semantic boundary):

```lean
fun n [NeZero n] self => self.10
```

### D080: `HighamBench.p09ApplyRoundedMixedRadixStages`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `61063d112f3c995286b019086986dcf63210bf1f5744acb8a92227c26e9fc09e`

Type:

```lean
{r n : Nat} →
  [inst : NeZero n] →
    HighamBench.P09WilkinsonModel → (Fin r → HighamBench.P09MixedRadixStage n) → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{r n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (model : HighamBench.P09WilkinsonModel) →
      (stages : Fin r → @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {r n} [NeZero n] model stages x =>
  List.foldl (fun state stage => HighamBench.p09RoundedMixedRadixStageApply model stage state) x (List.ofFn stages)
```

### D081: `HighamBench.p09MixedRadixBlockApply._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `7`
- Semantic SHA-256: `66982eaeb447cbce750fce4807c54ab59c13e01413ca8d08d2bf34da2ff6771f`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : HighamBench.P09MixedRadixStage n), NeZero stage.radix
```

Fully explicit type:

```lean
∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n]
  (stage : @HighamBench.P09MixedRadixStage n inst),
  @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
    (@HighamBench.P09MixedRadixStage.radix n inst stage)
```

### D082: `HighamBench.p09RoundedMixedRadixStageApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `8`
- Semantic SHA-256: `b4de5bf2de2ad2cbb3d8cfee33f114fd36d13ea12e460ba2195b402663249c1d`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    HighamBench.P09WilkinsonModel → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (model : HighamBench.P09WilkinsonModel) →
      (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x =>
  HighamBench.p09RoundedMixedRadixTwiddleApply model stage (HighamBench.p09RoundedMixedRadixBlockApply model stage x)
```

### D083: `HighamBench.p09RoundedMixedRadixBlockApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `3ec7290166ef53afdd08348156e26cd0cc09e178e2d1d2e5f6867d2e4285f21a`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    HighamBench.P09WilkinsonModel → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (model : HighamBench.P09WilkinsonModel) →
      (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x =>
  have permuted := fun i => x (EquivLike.toFunLike.coe stage.permutation i);
  fun i =>
  have bi := EquivLike.toFunLike.coe stage.reindex.symm i;
  if h2 : Eq stage.radix 2 then
    HighamBench.p09RoundedRadixTwoBlock model
      (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := Eq.rec j ⋯ }))
      (Eq.rec bi.snd h2)
  else
    if h4 : Eq stage.radix 4 then
      HighamBench.p09RoundedRadixFourBlock model
        (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := Eq.rec j ⋯ }))
        (Eq.rec bi.snd h4)
    else
      HighamBench.p09RoundedGenericRadixBlock model
        (fun j => permuted (EquivLike.toFunLike.coe stage.reindex { fst := bi.fst, snd := j })) bi.snd
```

### D084: `HighamBench.p09RoundedMixedRadixTwiddleApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `9`
- Semantic SHA-256: `f82a1d5f9b23ae14e1beac36ee4b2eaedc7c5a5f46f4499a193d3b2f29b7ae73`

Type:

```lean
{n : Nat} →
  [inst : NeZero n] →
    HighamBench.P09WilkinsonModel → HighamBench.P09MixedRadixStage n → (ZMod n → Complex) → ZMod n → Complex
```

Fully explicit type:

```lean
{n : Nat} →
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    (model : HighamBench.P09WilkinsonModel) →
      (stage : @HighamBench.P09MixedRadixStage n inst) → (x : ZMod n → Complex) → ZMod n → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] model stage x i =>
  ite (Eq stage.useTwiddle Bool.true)
    (HighamBench.p09RoundedComplexMul model (HighamBench.p09RoundedRoot model (stage.twiddleExponent i)) (x i)) (x i)
```

### D085: `HighamBench.p09RoundedComplexMul`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `b93b10e70e4ca5713e6cc3f020f91d9daf574ecac767dd4fa20903c58c2fab0e`

Type:

```lean
HighamBench.P09WilkinsonModel → Complex → Complex → Complex
```

Fully explicit type:

```lean
(model : HighamBench.P09WilkinsonModel) → (x y : Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x y =>
  { re := model.flAdd (model.flMul x.re y.re) (Real.instNeg.neg (model.flMul x.im y.im)),
    im := model.flAdd (model.flMul x.re y.im) (model.flMul x.im y.re) }
```

### D086: `HighamBench.p09RoundedGenericRadixBlock`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `84ebda7f0ff318133fd19d36acaa11b1992ef0584beeb0859f5e9a6771660e61`

Type:

```lean
{q : Nat} → [NeZero q] → HighamBench.P09WilkinsonModel → (ZMod q → Complex) → ZMod q → Complex
```

Fully explicit type:

```lean
{q : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) q] →
    (model : HighamBench.P09WilkinsonModel) → (x : ZMod q → Complex) → (k : ZMod q) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model x k =>
  HighamBench.p09RoundedComplexSum model fun j =>
    HighamBench.p09RoundedComplexMul model (HighamBench.p09RoundedRoot model (instHMul.hMul j k)) (x j)
```

### D087: `HighamBench.p09RoundedMixedRadixBlockApply._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `10`
- Semantic SHA-256: `31b52ab0de107cfaac2abe09ac02426698622fa18c17b5517159dd8facd3a9cb`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : HighamBench.P09MixedRadixStage n), Eq stage.radix 2 → Eq 2 stage.radix
```

Fully explicit type:

```lean
∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n]
  (stage : @HighamBench.P09MixedRadixStage n inst)
  (h2 :
    @Eq.{1} Nat (@HighamBench.P09MixedRadixStage.radix n inst stage)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))),
  @Eq.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@HighamBench.P09MixedRadixStage.radix n inst stage)
```

### D088: `HighamBench.p09RoundedMixedRadixBlockApply._proof_2`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `10`
- Semantic SHA-256: `36c04751e7e69199fa2d88d60e3db54faf40e54416a6e4d0c808948aabd60c5b`

Type:

```lean
∀ {n : Nat} [inst : NeZero n] (stage : HighamBench.P09MixedRadixStage n), Eq stage.radix 4 → Eq 4 stage.radix
```

Fully explicit type:

```lean
∀ {n : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n]
  (stage : @HighamBench.P09MixedRadixStage n inst)
  (h4 :
    @Eq.{1} Nat (@HighamBench.P09MixedRadixStage.radix n inst stage)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@HighamBench.P09MixedRadixStage.radix n inst stage)
```

### D089: `HighamBench.p09RoundedRadixFourBlock`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `ba3f006d9032e7045e3bc4fd3080eaccb8160ccdc53642cc2770492ab10872de`

Type:

```lean
HighamBench.P09WilkinsonModel → (ZMod 4 → Complex) → ZMod 4 → Complex
```

Fully explicit type:

```lean
(model : HighamBench.P09WilkinsonModel) →
  (x : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Complex) →
    (k : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x k =>
  have index := (ZMod.finEquiv 4).toEquiv;
  have term := fun i =>
    HighamBench.p09RadixFourCoefficientApply (instHMul.hMul (EquivLike.toFunLike.coe index i) k)
      (x (EquivLike.toFunLike.coe index i));
  HighamBench.p09RoundedComplexAdd model (HighamBench.p09RoundedComplexAdd model (term 0) (term 1))
    (HighamBench.p09RoundedComplexAdd model (term 2) (term 3))
```

### D090: `HighamBench.p09RoundedRadixTwoBlock`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `763c4175157ca5bad026dfd600033c4c8ba290fc556e8d90fb929e74f74791ba`

Type:

```lean
HighamBench.P09WilkinsonModel → (ZMod 2 → Complex) → ZMod 2 → Complex
```

Fully explicit type:

```lean
(model : HighamBench.P09WilkinsonModel) →
  (x : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) →
    (k : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x k =>
  HighamBench.p09RoundedComplexSum model fun j => HighamBench.p09RadixTwoCoefficientApply (instHMul.hMul j k) (x j)
```

### D091: `HighamBench.p09RoundedRoot`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `10`
- Semantic SHA-256: `a6af37b386d000aa189d9da9937fcefac49c0085ff5de774b92de2619e0fdc9b`

Type:

```lean
{q : Nat} → [NeZero q] → HighamBench.P09WilkinsonModel → ZMod q → Complex
```

Fully explicit type:

```lean
{q : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) q] →
    (model : HighamBench.P09WilkinsonModel) → (j : ZMod q) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model j =>
  { re := model.flCos (HighamBench.p09RootAngle j), im := model.flSin (HighamBench.p09RootAngle j) }
```

### D092: `HighamBench.P09WilkinsonModel.flAdd`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `b938991e119b06301e2cd03fff62ec1cddff900aeeb08cb43310f9ffc480d8b0`

Type:

```lean
HighamBench.P09WilkinsonModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.5
```

### D093: `HighamBench.P09WilkinsonModel.flCos`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `72a3a0864d70744a999e06284a98176fab2e9c7b8debf6ec88e44bd0b8ba6de4`

Type:

```lean
HighamBench.P09WilkinsonModel → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.8
```

### D094: `HighamBench.P09WilkinsonModel.flMul`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `6d21356ec66cacf098051fc05ca9919a059a4a65a900eb3cc227bd26bee62a47`

Type:

```lean
HighamBench.P09WilkinsonModel → Real → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.6
```

### D095: `HighamBench.P09WilkinsonModel.flSin`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `38f27b8dcb3484eed14d8e2a32e4c6fa407c3ac190eef9ac592163ef83fe7312`

Type:

```lean
HighamBench.P09WilkinsonModel → Real → Real
```

Fully explicit type:

```lean
(self : HighamBench.P09WilkinsonModel) → Real → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.7
```

### D096: `HighamBench.p09RadixFourCoefficientApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `d7c3aaaa2d06ac8c4c1c139aee3d77d883674575ca9ce14ee4b18016db1fad79`

Type:

```lean
ZMod 4 → Complex → Complex
```

Fully explicit type:

```lean
(j : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → (x : Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun j x =>
  ite (Eq j 0) x
    (ite (Eq j 1) { re := Real.instNeg.neg x.im, im := x.re }
      (ite (Eq j 2) (Complex.instNeg.neg x) { re := x.im, im := Real.instNeg.neg x.re }))
```

### D097: `HighamBench.p09RadixTwoCoefficientApply`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `428bc8f94723929b45fdb2bb504716bd8365b7563e491259d882896e7f032f20`

Type:

```lean
ZMod 2 → Complex → Complex
```

Fully explicit type:

```lean
(j : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) → (x : Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun j x => ite (Eq j 0) x (Complex.instNeg.neg x)
```

### D098: `HighamBench.p09RootAngle`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `46ff9a18b6c4b2cc32d5c954f428895ca4ab25a82e357b33d2062db8082f9ec5`

Type:

```lean
{q : Nat} → [NeZero q] → ZMod q → Real
```

Fully explicit type:

```lean
{q : Nat} → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) q] → (j : ZMod q) → Real
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] j => instHDiv.hDiv (instHMul.hMul (instHMul.hMul 2 Real.pi) j.val.cast) q.cast
```

### D099: `HighamBench.p09RoundedComplexAdd`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `afb354edb26d952dae0834da42cca39b5ba8e7594489e99bffa1c580295f95a4`

Type:

```lean
HighamBench.P09WilkinsonModel → Complex → Complex → Complex
```

Fully explicit type:

```lean
(model : HighamBench.P09WilkinsonModel) → (x y : Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun model x y => { re := model.flAdd x.re y.re, im := model.flAdd x.im y.im }
```

### D100: `HighamBench.p09RoundedComplexSum`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `947d8b493b9f83d1fee0edeb79367bf95e524991a119df339ba0ad45a661d4d3`

Type:

```lean
{q : Nat} → [NeZero q] → HighamBench.P09WilkinsonModel → (ZMod q → Complex) → Complex
```

Fully explicit type:

```lean
{q : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) q] →
    (model : HighamBench.P09WilkinsonModel) → (term : ZMod q → Complex) → Complex
```

Definition body (one-level semantic boundary):

```lean
fun {q} [NeZero q] model term =>
  have index := (ZMod.finEquiv q).toEquiv;
  { re := HighamBench.recursiveSum model.flAdd q fun i => (term (EquivLike.toFunLike.coe index i)).re,
    im := HighamBench.recursiveSum model.flAdd q fun i => (term (EquivLike.toFunLike.coe index i)).im }
```

### D101: `HighamBench.p09RoundedRadixFourBlock._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `11`
- Semantic SHA-256: `ed734b22ed9854026574c400f6f18f3f6f2ecba4c424c5f37b31a9c3161af165`

Type:

```lean
NeZero (instHAdd.hAdd 3 1)
```

Fully explicit type:

```lean
@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D102: `HighamBench.p09RoundedRadixTwoBlock._proof_1`

- Role: `local`
- Owner module: `HighamBench.P09Base`
- Declaration kind: `theorem`
- Distance from target type: `11`
- Semantic SHA-256: `fc07827897ea6ceaa43dcb4499d7aa2aacd83067423edb8ca73b7bb2f57ee423`

Type:

```lean
NeZero (instHAdd.hAdd 1 1)
```

Fully explicit type:

```lean
@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

### D103: `HighamBench.recursiveSum`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `3a24e7a5c707c014d59b9d90d536db1f1c79ef135d2ba34adb6af8a4258efe41`

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

### D104: `HighamBench.recursiveSum._proof_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `theorem`
- Distance from target type: `13`
- Semantic SHA-256: `7f01e5fdb761df0e050b0929b93312fc9084bc345726c816952ed0fd4844be27`

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

### D105: `HighamBench.recursiveSum.match_1`

- Role: `local`
- Owner module: `HighamBench.Core`
- Declaration kind: `abbrev`
- Distance from target type: `13`
- Semantic SHA-256: `56d4f4744c0103a83d3305dc49473baf5a72c1037bbec52ff87f6f4a5419f79e`

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

### D106: `And`

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

### D107: `DivInvMonoid.toDiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D108: `Exists`

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

### D109: `Fin`

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

### D110: `Fin.fintype`

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

### D111: `Finset.sum`

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

### D112: `Finset.univ`

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

### D113: `HAdd.hAdd`

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

### D114: `HDiv.hDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `1`
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

### D115: `HMul.hMul`

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

### D116: `HPow.hPow`

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

### D117: `LE.le`

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

### D118: `LT.lt`

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

### D119: `Monoid.toNatPow`

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

### D120: `MulZeroClass.toZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `1`
- Semantic SHA-256: `a3f3ff8a43fb45098d9029196fe0a081ace6a8cc0c485317c7c17e719ec29c60`

Type:

```lean
{M₀ : Type u} → [self : MulZeroClass M₀] → Zero M₀
```

Fully explicit type:

```lean
{M₀ : Type u} → [self : MulZeroClass.{u} M₀] → Zero.{u} M₀
```

Definition body (one-level semantic boundary):

```lean
fun M₀ [self : MulZeroClass M₀] => self.2
```

### D121: `Nat`

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

### D122: `Nat.instMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Nat`
- Declaration kind: `def`
- Distance from target type: `1`
- Semantic SHA-256: `4c01f1e84ffddbe4a96559f1586583d0f7f5960c7ff89d25625db97dd017d56c`

Type:

```lean
MulZeroClass Nat
```

Fully explicit type:

```lean
MulZeroClass.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ toMul := instMulNat, toZero := Nat.instAddMonoid.toAddZeroClass.toZero, zero_mul := Nat.zero_mul,
  mul_zero := Nat.mul_zero }
```

### D123: `NeZero`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `inductive`
- Distance from target type: `1`
- Semantic SHA-256: `b995ca083c15c268a4faa60a710cd8ff05c7de4dd8e301783fe0e0adeee47a06`

Type:

```lean
{R : Type u_1} → [Zero R] → R → Prop
```

Fully explicit type:

```lean
{R : Type u_1} → [Zero.{u_1} R] → (n : R) → Prop
```

### D124: `OfNat.ofNat`

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

### D125: `Real`

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

### D126: `Real.instAdd`

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

### D127: `Real.instAddCommMonoid`

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

### D128: `Real.instDivInvMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D129: `Real.instLE`

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

### D130: `Real.instLT`

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

### D131: `Real.instMonoid`

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

### D132: `Real.instMul`

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

### D133: `Real.instZero`

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

### D134: `Subtype.val`

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

### D135: `Zero.toOfNat0`

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

### D136: `instHAdd`

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

### D137: `instHDiv`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `1`
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

### D138: `instHMul`

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

### D139: `instHPow`

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

### D140: `instOfNatNat`

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

### D141: `Nat.cast`

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

### D142: `Real.instNatCast`

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

### D143: `Real.sqrt`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Sqrt`
- Declaration kind: `def`
- Distance from target type: `2`
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

### D144: `Subtype`

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

### D145: `AddCommMonoidWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `07f48d3cfc3c7c30b6298df8531409d9844ab8c7e0ba94dea2a3fd29879320af`

Type:

```lean
{R : Type u_2} → [self : AddCommMonoidWithOne R] → AddMonoidWithOne R
```

Fully explicit type:

```lean
{R : Type u_2} → [self : AddCommMonoidWithOne.{u_2} R] → AddMonoidWithOne.{u_2} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddCommMonoidWithOne R] => self.1
```

### D146: `AddMonoidWithOne.toNatCast`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `6b956e88ee642e7533983b76ff8087f4537eea04f025165ce1fa45dc80e795a2`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → NatCast R
```

Fully explicit type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne.{u_2} R] → NatCast.{u_2} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.1
```

### D147: `Complex`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `06f5db8f409d6076be5ab5a3405277f735e30c46762deb074e76e94ef07eb934`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D148: `Complex.instNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Norm`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `1cfad456b65aa5b5a2b02b8a83a1499ef6fccab64640c73c839132b51fed64cc`

Type:

```lean
Norm Complex
```

Fully explicit type:

```lean
Norm.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{ norm := fun z => (MonoidWithZeroHom.funLike.coe Complex.normSq z).sqrt }
```

### D149: `Complex.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `26cc7a92ad47bfd4a81e9b47e27ff96a00a409cbd8b04b21b458f7c67849aa8d`

Type:

```lean
Sub Complex
```

Fully explicit type:

```lean
Sub.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{ sub := fun z w => { re := instHSub.hSub z.re w.re, im := instHSub.hSub z.im w.im } }
```

### D150: `ENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `5b8f4d61311ebccecf6a54ceca44191d394e0108c8596129a77f03c15a7e457f`

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
WithTop NNReal
```

### D151: `Eq`

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

### D152: `Fin.instOfNat`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `8f9c302902ae8c66b3f71728ffe02994a026b562f27b9df8d4f84793e455e26b`

Type:

```lean
{n : Nat} → [NeZero n] → {i : Nat} → OfNat (Fin n) i
```

Fully explicit type:

```lean
{n : Nat} → [@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0))) n] → {i : Nat} → OfNat.{0} (Fin n) i
```

Definition body (one-level semantic boundary):

```lean
fun {n} [NeZero n] {i} => { ofNat := Fin.ofNat n i }
```

### D153: `Finset.prod`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.BigOperators.Group.Finset.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D154: `HSub.hSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
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

### D155: `Nat.below`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `04a84157ffe59e0d301c0043561b314a7ab23e9ec7be060ff84461bda2e48a65`

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

### D156: `Nat.brecOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `112a5e33ebc43ed10219858c8cc3892005a54c63ed7cb7590213f5a7791f9c14`

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

### D157: `Nat.instCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.Nat.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `d946a6ce034e0404ae6836f267c26c67248cfd19fa68c2f7b9e321695d4f7c86`

Type:

```lean
CommMonoid Nat
```

Fully explicit type:

```lean
CommMonoid.{0} Nat
```

Definition body (one-level semantic boundary):

```lean
{ mul := Nat.mul, mul_assoc := Nat.mul_assoc, one := Nat.zero.succ, one_mul := Nat.one_mul, mul_one := Nat.mul_one,
  npow := fun m n => instHPow.hPow n m, npow_zero := Nat.pow_zero, npow_succ := Nat.instCommMonoid._proof_1,
  mul_comm := Nat.mul_comm }
```

### D158: `Nat.ne_of_gt`

- Role: `external-frontier`
- Owner module: `Init.Data.Nat.Basic`
- Declaration kind: `theorem`
- Distance from target type: `3`
- Semantic SHA-256: `efc85b6e2ba577017c57d5b88a2d6f39eaa33310359c247b44f3ff338427ac62`

Type:

```lean
∀ {a b : Nat}, instLTNat.lt b a → Ne a b
```

Fully explicit type:

```lean
∀ {a b : Nat} (h : @LT.lt.{0} Nat instLTNat b a), @Ne.{1} Nat a b
```

### D159: `Nat.succ`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `c069f332a974e3dbf1dc48acb0a49ab7d732c776b5cccdbe836db99ce812bdb2`

Type:

```lean
Nat → Nat
```

Fully explicit type:

```lean
(n : Nat) → Nat
```

### D160: `NeZero.mk`

- Role: `external-frontier`
- Owner module: `Init.Data.NeZero`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `e2e32989d835a09f096b510efd93c48c325d5131f0dc0608e4b63d8e6448d9ad`

Type:

```lean
∀ {R : Type u_1} [inst : Zero R] {n : R}, Ne n 0 → NeZero n
```

Fully explicit type:

```lean
∀ {R : Type u_1} [inst : Zero.{u_1} R] {n : R}
  (out : @Ne.{u_1 + 1} R n (@OfNat.ofNat.{u_1} R (nat_lit 0) (@Zero.toOfNat0.{u_1} R inst))), @NeZero.{u_1} R inst n
```

### D161: `Norm.norm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `3`
- Semantic SHA-256: `25f5aa97df9bb1faeacd7e5e6446ecbd367452a7105f098063355423713fe15a`

Type:

```lean
{E : Type u_8} → [self : Norm E] → E → Real
```

Fully explicit type:

```lean
{E : Type u_8} → [self : Norm.{u_8} E] → E → Real
```

Definition body (one-level semantic boundary):

```lean
fun E [self : Norm E] => self.1
```

### D162: `One.toOfNat1`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D163: `PiLp.instNorm`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.PiLp`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `f24beda1ba0ca545fc281a05cd134dcc3c729e2eabbfac59f4340d15384ca425`

Type:

```lean
(p : ENNReal) → {ι : Type u_2} → (β : ι → Type u_4) → [Fintype ι] → [(i : ι) → Norm (β i)] → Norm (PiLp p β)
```

Fully explicit type:

```lean
(p : ENNReal) →
  {ι : Type u_2} →
    (β : ι → Type u_4) → [Fintype.{u_2} ι] → [(i : ι) → Norm.{u_4} (β i)] → Norm.{max u_4 u_2} (@PiLp.{u_2, u_4} p ι β)
```

Definition body (one-level semantic boundary):

```lean
fun p {ι} β [Fintype ι] [inst_1 : (i : ι) → Norm (β i)] =>
  {
    norm := fun f =>
      ite (Eq p 0) ⋯.toFinset.card.cast
        (ite (Eq p instTopENNReal.top) (iSup fun i => (inst_1 i).norm (f.ofLp i))
          (instHPow.hPow (Finset.univ.sum fun i => instHPow.hPow ((inst_1 i).norm (f.ofLp i)) p.toReal)
            (instHDiv.hDiv 1 p.toReal))) }
```

### D164: `Real.instOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D165: `Real.instSub`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D166: `WithLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `inductive`
- Distance from target type: `3`
- Semantic SHA-256: `beeca7e7d011bf353b991ee4fb3bf57a00fca40fd553001d24ad8181bda346e3`

Type:

```lean
ENNReal → Type u_1 → Type u_1
```

Fully explicit type:

```lean
(p : ENNReal) → (V : Type u_1) → Type u_1
```

### D167: `WithLp.toLp`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Lp.WithLp`
- Declaration kind: `constructor`
- Distance from target type: `3`
- Semantic SHA-256: `293799c52cddc04402243afb567ab5aa26e35f2b7064cbec3d87dc7fba0ba006`

Type:

```lean
(p : ENNReal) → {V : Type u_1} → V → WithLp p V
```

Fully explicit type:

```lean
(p : ENNReal) → {V : Type u_1} → (ofLp : V) → WithLp.{u_1} p V
```

### D168: `instAddCommMonoidWithOneENNReal`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ENNReal.Basic`
- Declaration kind: `def`
- Distance from target type: `3`
- Semantic SHA-256: `31d9551885e3007e5d1368365622cfd7638ea41cc6d885234041621de873f55c`

Type:

```lean
AddCommMonoidWithOne ENNReal
```

Fully explicit type:

```lean
AddCommMonoidWithOne.{0} ENNReal
```

Definition body (one-level semantic boundary):

```lean
WithTop.addCommMonoidWithOne
```

### D169: `instAddNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D170: `instHSub`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D171: `instLENat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D172: `instOfNatAtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `def`
- Distance from target type: `3`
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

### D173: `Fin.castLE`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `741eedcc1330cedb8ff0a69095d6df1438c40a8c734f1526dc385e45bb9ae135`

Type:

```lean
{n m : Nat} → instLENat.le n m → Fin n → Fin m
```

Fully explicit type:

```lean
{n m : Nat} → (h : @LE.le.{0} Nat instLENat n m) → (i : Fin n) → Fin m
```

Definition body (one-level semantic boundary):

```lean
fun {n m} h i => ⟨i.val, ⋯⟩
```

### D174: `Fin.mk`

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

### D175: `Fin.succ`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `72d7aaf169e5a264dac79e6aeec8a81c4436ffab27e5dbad2956eaeb4a147cad`

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
fun {n} x => Fin.succ.match_1 (fun x => Fin (instHAdd.hAdd n 1)) x fun i h => ⟨instHAdd.hAdd i 1, ⋯⟩
```

### D176: `Fin.val`

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

### D177: `Fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Defs`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `ff39697629d53c72a76ae41500ef08888ff834898920af48012f83225b729e55`

Type:

```lean
Type u_4 → Type u_4
```

Fully explicit type:

```lean
(α : Type u_4) → Type u_4
```

### D178: `Nat.AtLeastTwo`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Init`
- Declaration kind: `inductive`
- Distance from target type: `4`
- Semantic SHA-256: `318e11b8f9340f2f451d638786dd4fca470dece62824f4adc3bd18b5289aa911`

Type:

```lean
Nat → Prop
```

Fully explicit type:

```lean
(n : Nat) → Prop
```

### D179: `Nat.casesOn`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `ef6de7a898de834052ce3878aa9641c2b9e400122a4e012169c25b12d9da029d`

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

### D180: `Nat.decLt`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D181: `Not`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D182: `Pi.instFintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Fintype.Pi`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `38af89fa29e8604e3102e2493be25045731e11c8f462c08498d78926b091d1fa`

Type:

```lean
{α : Type u_3} →
  {β : α → Type u_4} → [DecidableEq α] → [Fintype α] → [(a : α) → Fintype (β a)] → Fintype ((a : α) → β a)
```

Fully explicit type:

```lean
{α : Type u_3} →
  {β : α → Type u_4} →
    [DecidableEq.{u_3 + 1} α] →
      [Fintype.{u_3} α] → [(a : α) → Fintype.{u_4} (β a)] → Fintype.{max u_3 u_4} ((a : α) → β a)
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] [Fintype α] [(a : α) → Fintype (β a)] =>
  { elems := Fintype.piFinset fun x => Finset.univ, complete := ⋯ }
```

### D183: `ZMod`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `16bf0604575e2049c78de15301315a487d981f9b4918a56c63dc9410569ff212`

Type:

```lean
Nat → Type
```

Fully explicit type:

```lean
Nat → Type
```

Definition body (one-level semantic boundary):

```lean
fun x => ZMod.match_1 (fun x => Type) x (fun _ => Int) fun n => Fin (instHAdd.hAdd n 1)
```

### D184: `ZMod.fintype`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `b61a1a310a01eaff03d99e3a9cee83c616fb078b27baacf352225f96ff75d7d7`

Type:

```lean
(n : Nat) → [NeZero n] → Fintype (ZMod n)
```

Fully explicit type:

```lean
(n : Nat) → [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] → Fintype.{0} (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  ZMod.fintype.match_1 (fun x x_2 => Fintype (ZMod x)) x x_1 (fun h => ⋯.elim) fun n x =>
    Fin.fintype (instHAdd.hAdd n 1)
```

### D185: `Zero.ofOfNat0`

- Role: `external-frontier`
- Owner module: `Init.Data.Zero`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `d610ee8a0a2a61b7850d6032e696e6ae93221da787dff4096e98d4122502f26d`

Type:

```lean
{α : Type u_1} → [OfNat α 0] → Zero α
```

Fully explicit type:

```lean
{α : Type u_1} → [OfNat.{u_1} α (nat_lit 0)] → Zero.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [OfNat α 0] => { zero := 0 }
```

### D186: `dite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D187: `inferInstance`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `4`
- Semantic SHA-256: `a035e8579f88a0c5ce0a542c50396cd8f34aa652df8abeec2eb80c43a343b97b`

Type:

```lean
{α : Sort u} → [i : α] → α
```

Fully explicit type:

```lean
{α : Sort u} → [i : α] → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [i : α] => i
```

### D188: `instDecidableEqFin`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
- Semantic SHA-256: `7f6d785554f797d18d5ae0b7475c25e8deca421e6ee688f036987ac99c66e1cd`

Type:

```lean
(n : Nat) → DecidableEq (Fin n)
```

Fully explicit type:

```lean
(n : Nat) → DecidableEq.{1} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun n i j =>
  instDecidableEqFin.match_1 n i j (fun x => Decidable (Eq i j)) (decEq i.val j.val) (fun h => Decidable.isTrue ⋯)
    fun h => Decidable.isFalse ⋯
```

### D189: `instDecidableEqNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D190: `instLTNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D191: `ite`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `4`
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

### D192: `AddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `4f50638d97f5d425f8c05152b76b46854b453bc1d6f50f0e215f12ac557f8270`

Type:

```lean
(A : Type u_1) → [AddMonoid A] → (M : Type u_2) → [Monoid M] → Type (max u_1 u_2)
```

Fully explicit type:

```lean
(A : Type u_1) → [AddMonoid.{u_1} A] → (M : Type u_2) → [Monoid.{u_2} M] → Type (max u_1 u_2)
```

### D193: `AddChar.instFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Group.AddChar`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `83e85a9db1d0e5ecf4333397f4d7bc036d1237ee1458184cbc4f34ac900b688e`

Type:

```lean
{A : Type u_1} → {M : Type u_3} → [inst : AddMonoid A] → [inst_1 : Monoid M] → FunLike (AddChar A M) A M
```

Fully explicit type:

```lean
{A : Type u_1} →
  {M : Type u_3} →
    [inst : AddMonoid.{u_1} A] →
      [inst_1 : Monoid.{u_3} M] →
        FunLike.{max (u_3 + 1) (u_1 + 1), u_1 + 1, u_3 + 1} (@AddChar.{u_1, u_3} A inst M inst_1) A M
```

Definition body (one-level semantic boundary):

```lean
fun {A} {M} [AddMonoid A] [Monoid M] => { coe := AddChar.toFun, coe_injective' := ⋯ }
```

### D194: `AddGroupWithOne.toAddMonoidWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Int.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ab901b5dbbaa698c61da5b353ee51145e713b8971414a6fdb991cde02b5cb677`

Type:

```lean
{R : Type u} → [self : AddGroupWithOne R] → AddMonoidWithOne R
```

Fully explicit type:

```lean
{R : Type u} → [self : AddGroupWithOne.{u} R] → AddMonoidWithOne.{u} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddGroupWithOne R] => self.2
```

### D195: `AddMonoidWithOne.toAddMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `4fa12ffa6a6fee7c2d3050177e382f5c7883895f706698d037c6b045bef31105`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → AddMonoid R
```

Fully explicit type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne.{u_2} R] → AddMonoid.{u_2} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.2
```

### D196: `Bool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `e95da6be35714acbe5505fa5c6ba913c979305a6d87f38e35096664b551ce829`

Type:

```lean
Type
```

Fully explicit type:

```lean
Type
```

### D197: `CommRing.toNonUnitalCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1c9ac43c2f2e02a3e345036ace32d209b04abe0516407e31bcb54ee4c7201d0d`

Type:

```lean
{α : Type u} → [s : CommRing α] → NonUnitalCommRing α
```

Fully explicit type:

```lean
{α : Type u} → [s : CommRing.{u} α] → NonUnitalCommRing.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [s : CommRing α] =>
  { toAddMonoid := s.toAddMonoid, toNeg := s.toNeg, toSub := s.toSub, sub_eq_add_neg := ⋯, zsmul := s.zsmul,
    zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, add_comm := ⋯, toMul := s.toMul,
    left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯, mul_comm := ⋯ }
```

### D198: `CommRing.toRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c018410d7cd7a0cf748bc89452a2d03cd223cfa1f0ad262b865497873fcc8648`

Type:

```lean
{α : Type u} → [self : CommRing α] → Ring α
```

Fully explicit type:

```lean
{α : Type u} → [self : CommRing.{u} α] → Ring.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : CommRing α] => self.1
```

### D199: `Complex.instMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `3907754dc21e8763597dbf54bef08573c003d8f4d8def69e55d2b222d3fe9015`

Type:

```lean
Mul Complex
```

Fully explicit type:

```lean
Mul.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{
  mul := fun z w =>
    { re := instHSub.hSub (instHMul.hMul z.re w.re) (instHMul.hMul z.im w.im),
      im := instHAdd.hAdd (instHMul.hMul z.re w.im) (instHMul.hMul z.im w.re) } }
```

### D200: `Complex.instNormedAddCommGroup`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Norm`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `016e82ad35ade5300cbdb12e36381b7f24f7d80411c91afa9ee359975ee96bd9`

Type:

```lean
NormedAddCommGroup Complex
```

Fully explicit type:

```lean
NormedAddCommGroup.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{ toFun := Complex.instNorm.norm, map_zero' := Complex.norm_map_zero'✝, add_le' := Complex.norm_add_le'✝,
    neg' := Complex.norm_neg'✝,
    eq_zero_of_map_eq_zero' := Complex.instNormedAddCommGroup._proof_1 }.toNormedAddCommGroup
```

### D201: `Complex.instNormedField`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `08caf8897c319d3b5d8e17da052a9444ceb5f7bcaf585d54f79028085ec6333f`

Type:

```lean
NormedField Complex
```

Fully explicit type:

```lean
NormedField.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{ toNorm := Complex.instNorm, toField := Complex.instField,
  toMetricSpace := Complex.instNormedAddCommGroup.toMetricSpace, dist_eq := Complex.instNormedField._proof_1,
  norm_mul := Complex.norm_mul }
```

### D202: `Complex.instSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `008d132dd980a88182937c2214239a242f0e05220ab73a658ec569ddc4ad3f3e`

Type:

```lean
Semiring Complex
```

Fully explicit type:

```lean
Semiring.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
inferInstance
```

### D203: `DFunLike.coe`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
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

### D204: `Decidable.decide`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ff90c894e4369b89945915c4c814dd76d90e450369a804cfc4139fada64048b2`

Type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Fully explicit type:

```lean
(p : Prop) → [h : Decidable p] → Bool
```

Definition body (one-level semantic boundary):

```lean
fun p [h : Decidable p] => Decidable.casesOn h (fun x => Bool.false) fun x => Bool.true
```

### D205: `Distrib.toMul`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1d05ddf657021fb5615c5054f46b4863aec4ca856ca48fbb75add25e1f0fe06f`

Type:

```lean
{R : Type u_1} → [self : Distrib R] → Mul R
```

Fully explicit type:

```lean
{R : Type u_1} → [self : Distrib.{u_1} R] → Mul.{u_1} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : Distrib R] => self.1
```

### D206: `ENormedAddCommMonoid.toESeminormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `7d58c19063063d627291b91068fa4bf2bf5ff88679897376ac465b9f52e93642`

Type:

```lean
{E : Type u_8} → {inst : TopologicalSpace E} → [self : ENormedAddCommMonoid E] → ESeminormedAddCommMonoid E
```

Fully explicit type:

```lean
{E : Type u_8} →
  {inst : TopologicalSpace.{u_8} E} →
    [self : @ENormedAddCommMonoid.{u_8} E inst] → @ESeminormedAddCommMonoid.{u_8} E inst
```

Definition body (one-level semantic boundary):

```lean
fun E {inst} [self : ENormedAddCommMonoid E] => self.1
```

### D207: `ESeminormedAddCommMonoid.toAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `38db724db757c42f8e8affdaa0b60310db98b78e8ba320c452775788f7191220`

Type:

```lean
{E : Type u_8} → [inst : TopologicalSpace E] → [self : ESeminormedAddCommMonoid E] → AddCommMonoid E
```

Fully explicit type:

```lean
{E : Type u_8} →
  [inst : TopologicalSpace.{u_8} E] → [self : @ESeminormedAddCommMonoid.{u_8} E inst] → AddCommMonoid.{u_8} E
```

Definition body (one-level semantic boundary):

```lean
fun E [TopologicalSpace E] self => { toAddMonoid := self.toAddMonoid, add_comm := ⋯ }
```

### D208: `Equiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `inductive`
- Distance from target type: `5`
- Semantic SHA-256: `d7f2b85e220b17e17ce92ad10d5015da5d4751cd914568e619a1f288341c64e3`

Type:

```lean
Sort u_1 → Sort u_2 → Sort (max (max 1 u_1) u_2)
```

Fully explicit type:

```lean
(α : Sort u_1) → (β : Sort u_2) → Sort (max (max 1 u_1) u_2)
```

### D209: `Fin.castSucc`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1a33a8aafc4da9c57254d511b91e1e2a293b6b2e6a304786fbdb535a2fe20bc6`

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

### D210: `Fin.last`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `b7cf2c761ad02a28a34dfdeee30ac4ec7bd4c3ff77700313e3ed2f37d473f5f2`

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

### D211: `Function.Surjective`

- Role: `external-frontier`
- Owner module: `Init.Data.Function`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `445be13b68e9dc4df2e669e26d66cfeb452be0838a57a48f28fe13bacbab89c0`

Type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop
```

Fully explicit type:

```lean
{α : Sort u_1} → {β : Sort u_2} → (f : α → β) → Prop
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f => ∀ (b : β), Exists fun a => Eq (f a) b
```

### D212: `Function.update`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Function.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `092e6c4864b94365603f748d7cf0dd798223b04b127d4c37969b0c09cac29193`

Type:

```lean
{α : Sort u} → {β : α → Sort v} → [DecidableEq α] → ((a : α) → β a) → (a' : α) → β a' → (a : α) → β a
```

Fully explicit type:

```lean
{α : Sort u} → {β : α → Sort v} → [DecidableEq.{u} α] → (f : (a : α) → β a) → (a' : α) → (v : β a') → (a : α) → β a
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} [DecidableEq α] f a' v a => if h : Eq a a' then Eq.ndrec v ⋯ else f a
```

### D213: `MonoidWithZero.toMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.GroupWithZero.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `c0f91ccdc0415c148969849b7a83ce67d87cf4c402704186fa19f6313928d90f`

Type:

```lean
{M₀ : Type u} → [self : MonoidWithZero M₀] → Monoid M₀
```

Fully explicit type:

```lean
{M₀ : Type u} → [self : MonoidWithZero.{u} M₀] → Monoid.{u} M₀
```

Definition body (one-level semantic boundary):

```lean
fun M₀ [self : MonoidWithZero M₀] => self.1
```

### D214: `NonUnitalCommRing.toNonUnitalNonAssocCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `3bd70454a5180abed6221bb3f73922ebc30c10136298d23eb30d358cdd2fdb82`

Type:

```lean
{α : Type u} → [self : NonUnitalCommRing α] → NonUnitalNonAssocCommRing α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalCommRing.{u} α] → NonUnitalNonAssocCommRing.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toNonUnitalNonAssocRing := self.toNonUnitalNonAssocRing, mul_comm := ⋯ }
```

### D215: `NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `1082112ee2b1424cb7e1eff69df85640d23793811157d8a4401f364710bc21d2`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing α] → NonUnitalNonAssocRing α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocCommRing.{u} α] → NonUnitalNonAssocRing.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : NonUnitalNonAssocCommRing α] => self.1
```

### D216: `NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `ffc3b0b49d777bb976662d9282026e03ef869205e45f90008bd1659a4e78f2d7`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocRing α] → NonUnitalNonAssocSemiring α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocRing.{u} α] → NonUnitalNonAssocSemiring.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toAddMonoid := self.toAddMonoid, add_comm := ⋯, toMul := self.toMul, left_distrib := ⋯, right_distrib := ⋯,
    zero_mul := ⋯, mul_zero := ⋯ }
```

### D217: `NonUnitalNonAssocSemiring.toDistrib`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `5b49ec28e539eea6192ab07a9aee6da537ed1b5e017f2b9ef44d3a0ae51d79c6`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → Distrib α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring.{u} α] → Distrib.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toMul := self.toMul, toAdd := self.toAdd, left_distrib := ⋯, right_distrib := ⋯ }
```

### D218: `NormedAddCommGroup.toENormedAddCommMonoid`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Group.Continuity`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `eac639a9ae15f19554f668c9811538a135f4f05df04330bd8145b300efe57cfb`

Type:

```lean
{E : Type u_4} → [inst : NormedAddCommGroup E] → ENormedAddCommMonoid E
```

Fully explicit type:

```lean
{E : Type u_4} →
  [inst : NormedAddCommGroup.{u_4} E] →
    @ENormedAddCommMonoid.{u_4} E
      (@UniformSpace.toTopologicalSpace.{u_4} E
        (@PseudoMetricSpace.toUniformSpace.{u_4} E
          (@SeminormedAddCommGroup.toPseudoMetricSpace.{u_4} E
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{u_4} E inst))))
```

Definition body (one-level semantic boundary):

```lean
fun {E} [inst : NormedAddCommGroup E] =>
  let __spread.0 := NormedAddGroup.toENormedAddMonoid;
  have __spread.1 := inst;
  { toESeminormedAddMonoid := __spread.0.toESeminormedAddMonoid, add_comm := ⋯, enorm_eq_zero := ⋯ }
```

### D219: `NormedCommRing.toSeminormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `ad504b2606febc5a066d58ac540c9826bd1b7fce734d59a7fef63c7c27112fe3`

Type:

```lean
{α : Type u_2} → [β : NormedCommRing α] → SeminormedCommRing α
```

Fully explicit type:

```lean
{α : Type u_2} → [β : NormedCommRing.{u_2} α] → SeminormedCommRing.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [β : NormedCommRing α] =>
  { toNorm := β.toNorm, toRing := β.toRing, toPseudoMetricSpace := β.toPseudoMetricSpace, dist_eq := ⋯,
    norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D220: `NormedField.toNormedCommRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Field.Basic`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `4aa3dba57859ca72552799005279a2b5a65b8c083980070fbbff11fd1de56dec`

Type:

```lean
{α : Type u_2} → [NormedField α] → NormedCommRing α
```

Fully explicit type:

```lean
{α : Type u_2} → [NormedField.{u_2} α] → NormedCommRing.{u_2} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} [inst : NormedField α] =>
  let __src := inst;
  { toNorm := __src.toNorm, toRing := __src.toRing, toMetricSpace := __src.toMetricSpace, dist_eq := ⋯,
    norm_mul_le := ⋯, mul_comm := ⋯ }
```

### D221: `PseudoMetricSpace.toUniformSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.MetricSpace.Pseudo.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `a6831039b3ad5e37bd0e7692fd995a699d8bef791976e20262da929990521799`

Type:

```lean
{α : Type u} → [self : PseudoMetricSpace α] → UniformSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : PseudoMetricSpace.{u} α] → UniformSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : PseudoMetricSpace α] => self.7
```

### D222: `Real.cos`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `1377d30c9decd42f763baf8cb45f365ee121aec3ccf9f371c298d2926eba5a53`

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
fun x => (Complex.cos (Complex.ofReal x)).re
```

### D223: `Real.instAddGroup`

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

### D224: `Real.lattice`

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

### D225: `Real.sin`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Complex.Trigonometric`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `7937a67d5952a981d1a70df574b1d79c6e87542f5d15a2b0fe35a8fe8d31811f`

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
fun x => (Complex.sin (Complex.ofReal x)).re
```

### D226: `Ring.toAddGroupWithOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `d15833ebecad60e5e3b68aad85ba35db45194f877d115020c7add9b4f99d6aaf`

Type:

```lean
{R : Type u} → [self : Ring R] → AddGroupWithOne R
```

Fully explicit type:

```lean
{R : Type u} → [self : Ring.{u} R] → AddGroupWithOne.{u} R
```

Definition body (one-level semantic boundary):

```lean
fun R self =>
  { toIntCast := self.toIntCast, toNatCast := self.toNatCast, toAddMonoid := self.toAddMonoid, toOne := self.toOne,
    natCast_zero := ⋯, natCast_succ := ⋯, toNeg := self.toNeg, toSub := self.toSub, sub_eq_add_neg := ⋯,
    zsmul := self.zsmul, zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯, intCast_ofNat := ⋯,
    intCast_negSucc := ⋯ }
```

### D227: `SeminormedCommRing.toSeminormedRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e3cbc92d1d5e37d9eaeb1d595c83a78f7af7e3a8d249a700fa3676ab4e0c3d60`

Type:

```lean
{α : Type u_5} → [self : SeminormedCommRing α] → SeminormedRing α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : SeminormedCommRing.{u_5} α] → SeminormedRing.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedCommRing α] => self.1
```

### D228: `SeminormedRing.toPseudoMetricSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.Normed.Ring.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `e6ea9296e8643d5ae7cf334c065c9d6ebe4a95de22d3b0708a585db80e17322a`

Type:

```lean
{α : Type u_5} → [self : SeminormedRing α] → PseudoMetricSpace α
```

Fully explicit type:

```lean
{α : Type u_5} → [self : SeminormedRing.{u_5} α] → PseudoMetricSpace.{u_5} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : SeminormedRing α] => self.3
```

### D229: `Semiring.toMonoidWithZero`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `bf0d463c55fbfcd762eb28ad6f1672fe482a72dfed67d13a797c09f1f0431e64`

Type:

```lean
{α : Type u} → [self : Semiring α] → MonoidWithZero α
```

Fully explicit type:

```lean
{α : Type u} → [self : Semiring.{u} α] → MonoidWithZero.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self =>
  { toMul := self.toMul, mul_assoc := ⋯, toOne := self.toOne, one_mul := ⋯, mul_one := ⋯, npow := self.npow,
    npow_zero := ⋯, npow_succ := ⋯, toZero := self.toZero, zero_mul := ⋯, mul_zero := ⋯ }
```

### D230: `UniformSpace.toTopologicalSpace`

- Role: `external-frontier`
- Owner module: `Mathlib.Topology.UniformSpace.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `5`
- Semantic SHA-256: `4d18df801a98905221e0935ec2ddacda684a1430b8d198ebc23fad0643bce2a8`

Type:

```lean
{α : Type u} → [self : UniformSpace α] → TopologicalSpace α
```

Fully explicit type:

```lean
{α : Type u} → [self : UniformSpace.{u} α] → TopologicalSpace.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α [self : UniformSpace α] => self.1
```

### D231: `ZMod.commRing`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `15f1fcdfc5a4734b26869ae51723622c35f340d748486c74b75b03d93ed217af`

Type:

```lean
(n : Nat) → CommRing (ZMod n)
```

Fully explicit type:

```lean
(n : Nat) → CommRing.{0} (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun n =>
  { add := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instAdd.add fun n => Fin.instAdd.add,
    add_assoc := ⋯, zero := Nat.casesOn n 0 fun n => 0, zero_add := ⋯, add_zero := ⋯,
    nsmul :=
      Nat.casesOn (motive := fun x => Nat → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).nsmul fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).nsmul,
    nsmul_zero := ⋯, nsmul_succ := ⋯, add_comm := ⋯,
    mul := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instMul.mul fun n => Fin.instMul.mul,
    left_distrib := ⋯, right_distrib := ⋯, zero_mul := ⋯, mul_zero := ⋯, mul_assoc := ⋯,
    one := Nat.casesOn n 1 fun n => 1, one_mul := ⋯, mul_one := ⋯,
    natCast := Nat.casesOn (motive := fun x => Nat → ZMod x) n Nat.cast fun n => Nat.cast, natCast_zero := ⋯,
    natCast_succ := ⋯,
    npow :=
      Nat.casesOn (motive := fun x => Nat → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).npow fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).npow,
    npow_zero := ⋯, npow_succ := ⋯,
    neg := Nat.casesOn (motive := fun x => ZMod x → ZMod x) n Int.instNegInt.neg fun n => (Fin.neg n.succ).neg,
    sub := Nat.casesOn (motive := fun x => ZMod x → ZMod x → ZMod x) n Int.instSub.sub fun n => Fin.instSub.sub,
    sub_eq_add_neg := ⋯,
    zsmul :=
      Nat.casesOn (motive := fun x => Int → ZMod x → ZMod x) n (inferInstanceAs (CommRing Int)).zsmul fun n =>
        (inferInstanceAs (CommRing (Fin n.succ))).zsmul,
    zsmul_zero' := ⋯, zsmul_succ' := ⋯, zsmul_neg' := ⋯, neg_add_cancel := ⋯,
    intCast := Nat.casesOn (motive := fun x => Int → ZMod x) n (fun x => x) fun n => Int.cast, intCast_ofNat := ⋯,
    intCast_negSucc := ⋯, mul_comm := ⋯ }
```

### D232: `ZMod.stdAddChar`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`
- Declaration kind: `def`
- Distance from target type: `5`
- Semantic SHA-256: `d8823a1e47eaa4d04423dedbc65db89ecb2a2b5484d0ac20a437a96d1f98677a`

Type:

```lean
{N : Nat} → [NeZero N] → AddChar (ZMod N) Complex
```

Fully explicit type:

```lean
{N : Nat} →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) N] →
    @AddChar.{0, 0} (ZMod N)
      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod N)
        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod N)
          (@Ring.toAddGroupWithOne.{0} (ZMod N) (@CommRing.toRing.{0} (ZMod N) (ZMod.commRing N)))))
      Complex (@MonoidWithZero.toMonoid.{0} Complex (@Semiring.toMonoidWithZero.{0} Complex Complex.instSemiring))
```

Definition body (one-level semantic boundary):

```lean
fun {N} [NeZero N] => Circle.coeHom.compAddChar ZMod.toCircle
```

### D233: `abs`

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

### D234: `Equiv.instEquivLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D235: `EquivLike.toFunLike`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.FunLike.Equiv`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D236: `List.foldl`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `528cbed637e4ef546b621011d5cf13a5a950202dac919ee6cff2046010954d44`

Type:

```lean
{α : Type u} → {β : Type v} → (α → β → α) → α → List β → α
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (f : α → β → α) → (init : α) → List.{v} β → α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} f x x_1 =>
  List.brecOn (motive := fun x => α → α) x_1
    (fun x f_1 x_2 =>
      List.foldl.match_1 (fun x x_3 => List.below (motive := fun x => α → α) x_3 → α) x_2 x (fun a x => a)
        (fun a b l x => x.1 (f a b)) f_1)
    x
```

### D237: `List.ofFn`

- Role: `external-frontier`
- Owner module: `Init.Data.List.OfFn`
- Declaration kind: `def`
- Distance from target type: `6`
- Semantic SHA-256: `e54777dd091df49539c6c1473fd1928ad87f9e135ba5940e57702ecd3f83b095`

Type:

```lean
{α : Type u_1} → {n : Nat} → (Fin n → α) → List α
```

Fully explicit type:

```lean
{α : Type u_1} → {n : Nat} → (f : Fin n → α) → List.{u_1} α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {n} f => Fin.foldr n (fun x1 x2 => List.cons (f x1) x2) List.nil
```

### D238: `Ne`

- Role: `external-frontier`
- Owner module: `Init.Core`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D239: `Prod`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `inductive`
- Distance from target type: `6`
- Semantic SHA-256: `3df3b0cff45fb04022db70edff8e5747def6cae602cd8c33e673abac1bb4e347`

Type:

```lean
Type u → Type v → Type (max u v)
```

Fully explicit type:

```lean
(α : Type u) → (β : Type v) → Type (max u v)
```

### D240: `instMulNat`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `6`
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

### D241: `Bool.true`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `97e763ea95d8452117cf5762fd67acddd549677f08ccfa348c4bf23db7eaa9d8`

Type:

```lean
Bool
```

Fully explicit type:

```lean
Bool
```

### D242: `Equiv.symm`

- Role: `external-frontier`
- Owner module: `Mathlib.Logic.Equiv.Defs`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `57ee9c638939cfeecafbbd4c55de44dd6a442327ab164c9ed3cd729233289347`

Type:

```lean
{α : Sort u} → {β : Sort v} → Equiv α β → Equiv β α
```

Fully explicit type:

```lean
{α : Sort u} → {β : Sort v} → (e : Equiv.{u, v} α β) → Equiv.{v, u} β α
```

Definition body (one-level semantic boundary):

```lean
fun {α} {β} e => { toFun := e.invFun, invFun := e.toFun, left_inv := ⋯, right_inv := ⋯ }
```

### D243: `Prod.fst`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `31dfcc70f250d68311839281cfb552859ef6a5cdd31e725091d6a2a2f7fb2165`

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

### D244: `Prod.mk`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `7`
- Semantic SHA-256: `e42ba07a23655c2aae0502df1e03897313eaf034a0e84cfef98e91f6b4920097`

Type:

```lean
{α : Type u} → {β : Type v} → α → β → Prod α β
```

Fully explicit type:

```lean
{α : Type u} → {β : Type v} → (fst : α) → (snd : β) → Prod.{u, v} α β
```

### D245: `Prod.snd`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `7`
- Semantic SHA-256: `a70aebf9da319c4b02023421b33923182c4d5164c2087035016589b80ed1191a`

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

### D246: `instDecidableEqBool`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `def`
- Distance from target type: `7`
- Semantic SHA-256: `dedf43b35e221c78c811d0b7268b7be703d67b744ad16b23df01af14b2aa5899`

Type:

```lean
DecidableEq Bool
```

Fully explicit type:

```lean
DecidableEq.{1} Bool
```

Definition body (one-level semantic boundary):

```lean
Bool.decEq
```

### D247: `Eq.rec`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `recursor`
- Distance from target type: `10`
- Semantic SHA-256: `26d7c884de9aaebaff7a572e5e22744a04d3a3d7e18e61503180424e03b7c5b9`

Type:

```lean
{α : Sort u_1} →
  {a : α} → {motive : (a_1 : α) → Eq a a_1 → Sort u} → motive a ⋯ → {a_1 : α} → (t : Eq a a_1) → motive a_1 t
```

Fully explicit type:

```lean
{α : Sort u_1} →
  {a : α} →
    {motive : (a_1 : α) → (t : @Eq.{u_1} α a a_1) → Sort u} →
      (refl : motive a (@Eq.refl.{u_1} α a)) → {a_1 : α} → (t : @Eq.{u_1} α a a_1) → motive a_1 t
```

### D248: `Complex.im`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `276278e52acc5a079152e9d98e5089746dc087e625b4583f0c8a78b06f4e42ef`

Type:

```lean
Complex → Real
```

Fully explicit type:

```lean
(self : Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.2
```

### D249: `Complex.mk`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `constructor`
- Distance from target type: `11`
- Semantic SHA-256: `eb086afc5605d698a41cc0dbd78c60aa93ea5b91b09555f0a3d4205e5c8c3d6d`

Type:

```lean
Real → Real → Complex
```

Fully explicit type:

```lean
(re im : Real) → Complex
```

### D250: `Complex.re`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `d61ccb0f1eee778d5406d36759b34354009fc6e8d298adef3d9bfd8c57f16c75`

Type:

```lean
Complex → Real
```

Fully explicit type:

```lean
(self : Complex) → Real
```

Definition body (one-level semantic boundary):

```lean
fun self => self.1
```

### D251: `Distrib.toAdd`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `cf0362fc4cebf4743d0430077ad4081a1de510a75cfe1b4e6adc97f21271a3ba`

Type:

```lean
{R : Type u_1} → [self : Distrib R] → Add R
```

Fully explicit type:

```lean
{R : Type u_1} → [self : Distrib.{u_1} R] → Add.{u_1} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : Distrib R] => self.2
```

### D252: `Fin.instAdd`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `b3ee547a63794f701578ce9e2965118436a96f41dd67c398ae9c530ccaf94956`

Type:

```lean
{n : Nat} → Add (Fin n)
```

Fully explicit type:

```lean
{n : Nat} → Add.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { add := Fin.add }
```

### D253: `Fin.instMul`

- Role: `external-frontier`
- Owner module: `Init.Data.Fin.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `b2c82cb3bad8033084de1152c3311705f097fea4b09de861cfbc259aa58cae3d`

Type:

```lean
{n : Nat} → Mul (Fin n)
```

Fully explicit type:

```lean
{n : Nat} → Mul.{0} (Fin n)
```

Definition body (one-level semantic boundary):

```lean
fun {n} => { mul := Fin.mul }
```

### D254: `Neg.neg`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `abbrev`
- Distance from target type: `11`
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

### D255: `Real.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Real.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
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

### D256: `RingEquiv.toEquiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Equiv`
- Declaration kind: `abbrev`
- Distance from target type: `11`
- Semantic SHA-256: `ad2bbda4cee02ba76b521c1b90d73ae4e3d2edfd8e0e1471d3d872a8a791afb2`

Type:

```lean
{R : Type u_7} →
  {S : Type u_8} → [inst : Mul R] → [inst_1 : Mul S] → [inst_2 : Add R] → [inst_3 : Add S] → RingEquiv R S → Equiv R S
```

Fully explicit type:

```lean
{R : Type u_7} →
  {S : Type u_8} →
    [inst : Mul.{u_7} R] →
      [inst_1 : Mul.{u_8} S] →
        [inst_2 : Add.{u_7} R] →
          [inst_3 : Add.{u_8} S] →
            (self : @RingEquiv.{u_7, u_8} R S inst inst_1 inst_2 inst_3) → Equiv.{u_7 + 1, u_8 + 1} R S
```

Definition body (one-level semantic boundary):

```lean
fun R S [Mul R] [Mul S] [Add R] [Add S] self => self.1
```

### D257: `ZMod.finEquiv`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Basic`
- Declaration kind: `def`
- Distance from target type: `11`
- Semantic SHA-256: `c7185762b5ca67875cfbfd2fcf9c9669ff6295dab781a48d1dfda8dee8181f04`

Type:

```lean
(n : Nat) → [NeZero n] → RingEquiv (Fin n) (ZMod n)
```

Fully explicit type:

```lean
(n : Nat) →
  [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] →
    @RingEquiv.{0, 0} (Fin n) (ZMod n) (@Fin.instMul n)
      (@Distrib.toMul.{0} (ZMod n)
        (@NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n)
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n)
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} (ZMod n)
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} (ZMod n)
                (@CommRing.toNonUnitalCommRing.{0} (ZMod n) (ZMod.commRing n)))))))
      (@Fin.instAdd n)
      (@Distrib.toAdd.{0} (ZMod n)
        (@NonUnitalNonAssocSemiring.toDistrib.{0} (ZMod n)
          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} (ZMod n)
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} (ZMod n)
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} (ZMod n)
                (@CommRing.toNonUnitalCommRing.{0} (ZMod n) (ZMod.commRing n)))))))
```

Definition body (one-level semantic boundary):

```lean
fun x x_1 =>
  ZMod.finEquiv.match_1 (fun x x_2 => RingEquiv (Fin x) (ZMod x)) x x_1 (fun h => ⋯.elim) fun n x =>
    RingEquiv.refl (Fin (instHAdd.hAdd n 1))
```

### D258: `AddMonoidWithOne.toOne`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Nat.Cast.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `12`
- Semantic SHA-256: `2ee638fd7292dbcf1e4adb85b14bbd0f304e8a260316e61621bf8eac03f03f6d`

Type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne R] → One R
```

Fully explicit type:

```lean
{R : Type u_2} → [self : AddMonoidWithOne.{u_2} R] → One.{u_2} R
```

Definition body (one-level semantic boundary):

```lean
fun R [self : AddMonoidWithOne R] => self.3
```

### D259: `Complex.instNeg`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.Complex.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `5a2f4911bfc517e9691dcac1bf08b20c460e4df0b018a1f5ba049adbb5de99ae`

Type:

```lean
Neg Complex
```

Fully explicit type:

```lean
Neg.{0} Complex
```

Definition body (one-level semantic boundary):

```lean
{ neg := fun z => { re := Real.instNeg.neg z.re, im := Real.instNeg.neg z.im } }
```

### D260: `NonUnitalNonAssocSemiring.toMulZeroClass`

- Role: `external-frontier`
- Owner module: `Mathlib.Algebra.Ring.Defs`
- Declaration kind: `abbrev`
- Distance from target type: `12`
- Semantic SHA-256: `87ddc8012963f013675a2d3b6dbd069bd2e6eeeafa9e7aff6d92bfbf7d848152`

Type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring α] → MulZeroClass α
```

Fully explicit type:

```lean
{α : Type u} → [self : NonUnitalNonAssocSemiring.{u} α] → MulZeroClass.{u} α
```

Definition body (one-level semantic boundary):

```lean
fun α self => { toMul := self.toMul, toZero := self.toZero, zero_mul := ⋯, mul_zero := ⋯ }
```

### D261: `Real.pi`

- Role: `external-frontier`
- Owner module: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `d75a7e5ab21b9e0fa41907d3afec6d87f8f264e448c96b4fd69b77195bdbebac`

Type:

```lean
Real
```

Fully explicit type:

```lean
Real
```

Definition body (one-level semantic boundary):

```lean
instHMul.hMul 2 (Classical.choose Real.exists_cos_eq_zero)
```

### D262: `ZMod.decidableEq`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Defs`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `7fd304bbb6ed0755497ea3fc939287cfddd9667bc3c6f5612bca13081a5103ba`

Type:

```lean
(n : Nat) → DecidableEq (ZMod n)
```

Fully explicit type:

```lean
(n : Nat) → DecidableEq.{1} (ZMod n)
```

Definition body (one-level semantic boundary):

```lean
fun x =>
  ZMod.match_1 (fun x => DecidableEq (ZMod x)) x (fun _ => inferInstanceAs (DecidableEq Int)) fun n =>
    inferInstanceAs (DecidableEq (Fin (instHAdd.hAdd n 1)))
```

### D263: `ZMod.val`

- Role: `external-frontier`
- Owner module: `Mathlib.Data.ZMod.Basic`
- Declaration kind: `def`
- Distance from target type: `12`
- Semantic SHA-256: `09f4356e066f5ae3957dc3f413b65273a0bf2b1f5828e9b1cfc9e08f21266213`

Type:

```lean
{n : Nat} → ZMod n → Nat
```

Fully explicit type:

```lean
{n : Nat} → ZMod n → Nat
```

Definition body (one-level semantic boundary):

```lean
fun x => ZMod.val.match_1 (fun x => ZMod x → Nat) x (fun _ => Int.natAbs) fun n => Fin.val
```

### D264: `Nat.zero`

- Role: `external-frontier`
- Owner module: `Init.Prelude`
- Declaration kind: `constructor`
- Distance from target type: `14`
- Semantic SHA-256: `514797223f88553aabb4307fa99de406677fb8a482f74b8d4694356cbd803a51`

Type:

```lean
Nat
```

Fully explicit type:

```lean
Nat
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

### `HighamBench.P09Base`

Path: `paper_bencmark/highambench/shared/HighamBench/P09Base.lean`
SHA-256: `c8439b47cac51d982ae641b8b3f3dc9d3963841e856cd6643e8a5790dbc3a5ad`

```lean
import HighamBench.Core
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HighamBench

open scoped BigOperators

/-- Real matrix-vector action used for the paper's real-equivalent FFT analysis. -/
noncomputable def p09MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- Transpose in the paper-scoped real matrix notation. -/
def p09Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A j i

/-- Scalar multiplication of a paper-scoped real matrix. -/
def p09ScaleMatrix {n : ℕ}
    (s : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ s * A i j

/-- A candidate `Ainv` is a left inverse of `A`. -/
def p09IsLeftInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, Ainv i k * A k j = if i = j then 1 else 0

/-- A candidate `Ainv` is a right inverse of `A`. -/
def p09IsRightInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, A i k * Ainv k j = if i = j then 1 else 0

/-- Orthogonality of the normalized real-equivalent Fourier action. -/
def p09Orthogonal {n : ℕ} (Q : Fin n → Fin n → ℝ) : Prop :=
  p09IsLeftInverse Q (p09Transpose Q) ∧
    p09IsRightInverse Q (p09Transpose Q)

/-- Squared Euclidean norm of a finite real vector. -/
noncomputable def p09VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ 2

/-- Euclidean norm of a finite real vector. -/
noncomputable def p09VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p09VecNorm2Sq x)

/-- Root-mean-square value used throughout the paper. -/
noncomputable def p09Rms {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  p09VecNorm2 x / Real.sqrt (n : ℝ)

/-- Maximum absolute coordinate of a finite real vector. -/
noncomputable def p09Max {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

/-- Coordinatewise sum of a finite family of error vectors. -/
noncomputable def p09VectorSum {m n : ℕ}
    (term : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ ∑ i : Fin m, term i j

/-! ## Ramos's complex mixed-radix FFT setting -/

/-- The positive-sign, unnormalized complex Fourier transform from equation
`(1.1)`. Indexing by `ZMod n` is the zero-based cyclic indexing of the paper. -/
noncomputable def p09FourierTransform {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun k ↦ ∑ j : ZMod n, ZMod.stdAddChar (j * k) * x j

/-- The kernel used above has Ramos's positive exponential sign. -/
theorem p09StdAddChar_positive_exp {n : ℕ} [NeZero n] (j : ZMod n) :
    ZMod.stdAddChar j =
      Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / (n : ℂ)) := by
  rw [← ZMod.natCast_zmod_val j]
  simpa using (ZMod.stdAddChar_coe (N := n) (j.val : ℤ))

/-- Coordinatewise addition of complex vectors. -/
def p09ComplexVecAdd {n : ℕ} (x y : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x i + y i

/-- Coordinatewise subtraction of complex vectors. -/
def p09ComplexVecSub {n : ℕ} (x y : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x i - y i

/-- Squared Euclidean norm of a complex vector. -/
noncomputable def p09ComplexNorm2Sq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  ∑ i : ZMod n, ‖x i‖ ^ 2

/-- Euclidean norm of a complex vector. -/
noncomputable def p09ComplexNorm2 {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  Real.sqrt (p09ComplexNorm2Sq x)

/-- Ramos's `1 / sqrt n`-normalized RMS norm for complex vectors. -/
noncomputable def p09ComplexRms {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  p09ComplexNorm2 x / Real.sqrt (n : ℝ)

/-- Ramos's maximum component magnitude for a complex vector. -/
noncomputable def p09ComplexMax {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ ‖x i‖

/-- Every component magnitude is bounded by Ramos's explicit finite maximum. -/
theorem p09ComplexNorm_le_max {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) (i : ZMod n) :
    ‖x i‖ ≤ p09ComplexMax x := by
  exact Finset.le_sup' (fun j : ZMod n ↦ ‖x j‖) (Finset.mem_univ i)

/-- The piecewise local FFT constant `alpha(q)` in Theorem 1. -/
noncomputable def p09Alpha (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then Real.sqrt 2
  else if q = 4 then 5
  else 2 * Real.sqrt q * ((q : ℝ) + γ)

/-- The two FFT variants covered by the factorization discussion after
equation `(2.2)`. -/
inductive P09FftVariant
  | cooleyTukey
  | sandeTukey
  deriving DecidableEq

/-- One exact `D_l B_l P_l` factor in Ramos's mixed-radix factorization.
`reindex` identifies the repeated Fourier blocks and `twiddleExponent`
records the exact roots of unity on the diagonal factor. -/
structure P09MixedRadixStage (n : ℕ) [NeZero n] where
  radix : ℕ
  radix_two_le : 2 ≤ radix
  radix_ne_zero : radix ≠ 0
  blockCount : ℕ
  blockCount_ne_zero : blockCount ≠ 0
  order_eq : blockCount * radix = n
  reindex : Fin blockCount × ZMod radix ≃ ZMod n
  permutation : ZMod n ≃ ZMod n
  useTwiddle : Bool
  twiddleExponent : ZMod n → ZMod n

instance p09MixedRadixStageRadixNeZero {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) : NeZero stage.radix :=
  ⟨stage.radix_ne_zero⟩

/-- Exact action of the block-Fourier part `B_l P_l` of one mixed-radix
factor. -/
noncomputable def p09MixedRadixBlockApply {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  exact fun i ↦
    let bi := stage.reindex.symm i
    ∑ j : ZMod stage.radix,
      ZMod.stdAddChar (j * bi.2) * permuted (stage.reindex (bi.1, j))

/-- Exact action of the optional diagonal twiddle factor `D_l`. -/
noncomputable def p09MixedRadixTwiddleApply {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦
    if stage.useTwiddle then
      ZMod.stdAddChar (stage.twiddleExponent i) * x i
    else x i

/-- Exact action of one mixed-radix FFT factor. -/
noncomputable def p09MixedRadixStageApply {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p09MixedRadixTwiddleApply stage (p09MixedRadixBlockApply stage x)

/-- Sequential application of the exact mixed-radix factors, in execution
order from the input toward the output. -/
noncomputable def p09ApplyMixedRadixStages {m n : ℕ} [NeZero n]
    (stages : Fin m → P09MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  (List.ofFn stages).foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x

/-- Exact application of a permutation factor. -/
def p09Permute {n : ℕ} (permutation : ZMod n ≃ ZMod n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x (permutation i)

/-- A certified mixed-radix factorization of the paper's fixed Fourier
transform. The final two fields record the standard surjectivity and RMS
scaling facts for this exact unnormalized transform. -/
structure P09MixedRadixFftPlan (n : ℕ) [NeZero n] where
  stageCount : ℕ
  stageCount_pos : 0 < stageCount
  stage : Fin stageCount → P09MixedRadixStage n
  order_factorization : (∏ i : Fin stageCount, (stage i).radix) = n
  twiddle_pattern : ∀ i : Fin stageCount,
    (stage i).useTwiddle = decide (i.val + 1 < stageCount)
  finalPermutation : ZMod n ≃ ZMod n
  variant : P09FftVariant
  exact_factorization : ∀ x : ZMod n → ℂ,
    p09Permute finalPermutation (p09ApplyMixedRadixStages stage x) =
      p09FourierTransform x
  stage_norm_scaling : ∀ i : Fin stageCount, ∀ x : ZMod n → ℂ,
    p09ComplexNorm2 (p09MixedRadixStageApply (stage i) x) =
      Real.sqrt ((stage i).radix : ℝ) * p09ComplexNorm2 x
  fourier_surjective : Function.Surjective
    (p09FourierTransform : (ZMod n → ℂ) → ZMod n → ℂ)
  fourier_rms_scaling : ∀ x : ZMod n → ℂ,
    p09ComplexRms (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexRms x

/-- Ramos's exact mixed-radix constant
`K(N,gamma) = sum alpha(N_l) + (M-1)(3+2 gamma)`. -/
noncomputable def p09K {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) : ℝ :=
  (∑ i : Fin plan.stageCount, p09Alpha (plan.stage i).radix γ) +
    ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ)

/-- Wilkinson's scalar operation and absolute trigonometric-error model used
in Section 3. It is a real-number model and therefore does not add semantics
for overflow, underflow, NaN, infinities, or subnormals. -/
structure P09WilkinsonModel where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  gamma : ℝ
  gamma_nonneg : 0 ≤ gamma
  flAdd : ℝ → ℝ → ℝ
  flMul : ℝ → ℝ → ℝ
  flSin : ℝ → ℝ
  flCos : ℝ → ℝ
  flInput : ℂ → ℂ
  add_model : ∀ a b : ℝ, ∃ θa θb : ℝ,
    |θa| ≤ 1 ∧ |θb| ≤ 1 ∧
      flAdd a b = a * (1 + θa * epsilon) + b * (1 + θb * epsilon)
  mul_model : ∀ a b : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flMul a b = a * b * (1 + θ * epsilon)
  sin_model : ∀ a : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flSin a = Real.sin a + gamma * θ * epsilon
  cos_model : ∀ a : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flCos a = Real.cos a + gamma * θ * epsilon

/-- The positive root angle represented by a cyclic index. -/
noncomputable def p09RootAngle {q : ℕ} [NeZero q] (j : ZMod q) : ℝ :=
  2 * Real.pi * (j.val : ℝ) / (q : ℝ)

/-- A root of unity computed through the paper's sine and cosine operations. -/
noncomputable def p09RoundedRoot {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) : ℂ :=
  ⟨model.flCos (p09RootAngle j), model.flSin (p09RootAngle j)⟩

/-- Complex multiplication evaluated as four rounded real products followed by
two rounded real additions. Unary negation is exact in the real error model. -/
noncomputable def p09RoundedComplexMul (model : P09WilkinsonModel)
    (x y : ℂ) : ℂ :=
  ⟨model.flAdd (model.flMul x.re y.re) (-model.flMul x.im y.im),
    model.flAdd (model.flMul x.re y.im) (model.flMul x.im y.re)⟩

/-- Componentwise rounded addition used by the addition-only radix-2 and
radix-4 butterflies. -/
noncomputable def p09RoundedComplexAdd (model : P09WilkinsonModel)
    (x y : ℂ) : ℂ :=
  ⟨model.flAdd x.re y.re, model.flAdd x.im y.im⟩

/-- Sequential rounded summation of a complex vector. -/
noncomputable def p09RoundedComplexSum {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ) : ℂ :=
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  ⟨recursiveSum model.flAdd q fun i ↦ (term (index i)).re,
    recursiveSum model.flAdd q fun i ↦ (term (index i)).im⟩

/-- Multiplication by a radix-2 Fourier coefficient, implemented only by an
exact sign change. -/
def p09RadixTwoCoefficientApply (j : ZMod 2) (x : ℂ) : ℂ :=
  if j = 0 then x else -x

/-- Multiplication by a radix-4 Fourier coefficient, implemented by exact sign
changes and exchanges of real and imaginary components. -/
def p09RadixFourCoefficientApply (j : ZMod 4) (x : ℂ) : ℂ :=
  if j = 0 then x
  else if j = 1 then ⟨-x.im, x.re⟩
  else if j = 2 then -x
  else ⟨x.im, -x.re⟩

/-- Ramos's multiplication-free radix-2 Fourier block. -/
noncomputable def p09RoundedRadixTwoBlock (model : P09WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) : ℂ :=
  p09RoundedComplexSum model fun j ↦
    p09RadixTwoCoefficientApply (j * k) (x j)

/-- Ramos's multiplication-free radix-4 Fourier block. -/
noncomputable def p09RoundedRadixFourBlock (model : P09WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) : ℂ :=
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  p09RoundedComplexAdd model
    (p09RoundedComplexAdd model (term 0) (term 1))
    (p09RoundedComplexAdd model (term 2) (term 3))

/-- The radix-2 kernel is independent of rounded multiplication and
trigonometric evaluation. -/
theorem p09RoundedRadixTwoBlock_congr
    (model₁ model₂ : P09WilkinsonModel)
    (hadd : model₁.flAdd = model₂.flAdd)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    p09RoundedRadixTwoBlock model₁ x k =
      p09RoundedRadixTwoBlock model₂ x k := by
  simp [p09RoundedRadixTwoBlock, p09RoundedComplexSum, hadd]

/-- The radix-4 kernel is independent of rounded multiplication and
trigonometric evaluation. -/
theorem p09RoundedRadixFourBlock_congr
    (model₁ model₂ : P09WilkinsonModel)
    (hadd : model₁.flAdd = model₂.flAdd)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    p09RoundedRadixFourBlock model₁ x k =
      p09RoundedRadixFourBlock model₂ x k := by
  simp [p09RoundedRadixFourBlock, p09RoundedComplexAdd, hadd]

/-- A generic Fourier block. Unlike the special radix-2 and radix-4 kernels,
it computes roots and performs rounded complex multiplications. -/
noncomputable def p09RoundedGenericRadixBlock {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  p09RoundedComplexSum model fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)

/-- The operational block-Fourier part of one mixed-radix stage. Radix 2 and
radix 4 follow the paper's addition-only kernels; all other radices use the
generic trigonometric and complex-multiplication path. -/
noncomputable def p09RoundedMixedRadixBlockApply {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  exact fun i ↦
    let bi := stage.reindex.symm i
    if h2 : stage.radix = 2 then
      p09RoundedRadixTwoBlock model
        (fun j : ZMod 2 ↦
          permuted (stage.reindex (bi.1, h2.symm ▸ j)))
        (h2 ▸ bi.2)
    else if h4 : stage.radix = 4 then
      p09RoundedRadixFourBlock model
        (fun j : ZMod 4 ↦
          permuted (stage.reindex (bi.1, h4.symm ▸ j)))
        (h4 ▸ bi.2)
    else
      p09RoundedGenericRadixBlock model
        (fun j ↦ permuted (stage.reindex (bi.1, j))) bi.2

/-- The optional diagonal twiddle multiplication evaluated separately from the
block kernel, as in the constants stated after Theorem 1. -/
noncomputable def p09RoundedMixedRadixTwiddleApply {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦
    if stage.useTwiddle then
      p09RoundedComplexMul model
        (p09RoundedRoot model (stage.twiddleExponent i)) (x i)
    else x i

/-- One operational mixed-radix FFT stage: exact permutation, the appropriate
rounded block kernel, and then the separately evaluated optional twiddle. -/
noncomputable def p09RoundedMixedRadixStageApply {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p09RoundedMixedRadixTwiddleApply model stage
    (p09RoundedMixedRadixBlockApply model stage x)

/-- Sequential execution of all rounded mixed-radix stages. -/
noncomputable def p09ApplyRoundedMixedRadixStages {r n : ℕ} [NeZero n]
    (model : P09WilkinsonModel)
    (stages : Fin r → P09MixedRadixStage n) (x : ZMod n → ℂ) :
    ZMod n → ℂ :=
  (List.ofFn stages).foldl
    (fun state stage ↦ p09RoundedMixedRadixStageApply model stage state) x

/-- The operational one-dimensional FFT followed by its exact output
permutation. -/
noncomputable def p09RoundedFftApply {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p09Permute plan.finalPermutation
    (p09ApplyRoundedMixedRadixStages model plan.stage x)

/-- An operational trace of the one-dimensional floating-point FFT. Every
stage state is generated by the rounded operations above; no freely supplied
local error vector or per-instance remainder coefficient is admitted. -/
structure P09MixedRadixFftRun {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel) where
  input : ZMod n → ℂ
  stageState : ℕ → ZMod n → ℂ
  input_exact : ∀ i : ZMod n, model.flInput (input i) = input i
  initial_state : stageState 0 = input
  stage_step : ∀ i : Fin plan.stageCount,
    stageState (i.val + 1) =
      p09RoundedMixedRadixStageApply model (plan.stage i) (stageState i.val)

/-- The computed output obtained after all rounded stages and the exact final
permutation. -/
def p09FftComputedOutput {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) : ZMod n → ℂ :=
  p09Permute plan.finalPermutation (run.stageState plan.stageCount)

/-- The exact output roundoff error of a linked FFT execution. -/
noncomputable def p09FftRoundoffError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) : ZMod n → ℂ :=
  p09ComplexVecSub (p09FftComputedOutput run) (p09FourierTransform run.input)

/-- Positive roundoff parameters used to state right-sided asymptotics at
zero. -/
abbrev P09PositiveEpsilon := {ε : ℝ // 0 < ε}

/-- A family of operational FFT executions as machine precision tends to
zero. The plan, trigonometric constant, and exactly represented input are fixed
before `epsilon`; only the arithmetic model and its resulting trace vary. -/
structure P09AsymptoticFftFamily {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) where
  gamma_nonneg : 0 ≤ γ
  input : ZMod n → ℂ
  model : P09PositiveEpsilon → P09WilkinsonModel
  model_epsilon : ∀ ε, (model ε).epsilon = ε.1
  model_gamma : ∀ ε, (model ε).gamma = γ
  run : ∀ ε, P09MixedRadixFftRun plan (model ε)
  run_input : ∀ ε, (run ε).input = input

/-- The output roundoff error at one positive precision in an asymptotic
execution family. -/
noncomputable def p09FamilyFftRoundoffError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) (ε : P09PositiveEpsilon) :
    ZMod n → ℂ :=
  p09FftRoundoffError (family.run ε)

/-- Theorem 1(a) with the source's `O(epsilon^2)` interpreted on a right
neighborhood of zero for one fixed execution family. This result package is
constructed below from the separate predecessor estimates `(3.7)`--`(3.8)`. -/
structure P09TheoremOneRmsAsymptotic {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) where
  secondOrderCoeff : ℝ
  secondOrderCoeff_nonneg : 0 ≤ secondOrderCoeff
  radius : ℝ
  radius_pos : 0 < radius
  error_bound : ∀ ε : P09PositiveEpsilon, ε.1 ≤ radius →
    p09ComplexRms (p09FamilyFftRoundoffError family ε) ≤
      ε.1 * Real.sqrt (n : ℝ) * p09K plan γ *
          p09ComplexRms family.input +
        secondOrderCoeff * ε.1 ^ 2

/-! ### The stage-local derivation of Theorem 1(a) -/

/-- Apply a list of exact mixed-radix stages in execution order. -/
noncomputable def p09ApplyExactStageList {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun state stage ↦ p09MixedRadixStageApply stage state) x

private lemma p09MixedRadixStageApply_add {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixStageApply stage (p09ComplexVecAdd x y) =
      p09ComplexVecAdd (p09MixedRadixStageApply stage x)
        (p09MixedRadixStageApply stage y) := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  funext i
  simp only [p09MixedRadixStageApply, p09MixedRadixTwiddleApply,
    p09MixedRadixBlockApply, p09ComplexVecAdd]
  split_ifs <;> simp only [mul_add, Finset.sum_add_distrib]

private lemma p09ApplyExactStageList_add {n : ℕ} [NeZero n]
    (stages : List (P09MixedRadixStage n)) (x y : ZMod n → ℂ) :
    p09ApplyExactStageList stages (p09ComplexVecAdd x y) =
      p09ComplexVecAdd (p09ApplyExactStageList stages x)
        (p09ApplyExactStageList stages y) := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage stages ih =>
      simp only [p09ApplyExactStageList, List.foldl_cons]
      rw [p09MixedRadixStageApply_add]
      change p09ApplyExactStageList stages
          (p09ComplexVecAdd (p09MixedRadixStageApply stage x)
            (p09MixedRadixStageApply stage y)) = _
      exact ih _ _

private lemma p09Permute_add {n : ℕ} (permutation : ZMod n ≃ ZMod n)
    (x y : ZMod n → ℂ) :
    p09Permute permutation (p09ComplexVecAdd x y) =
      p09ComplexVecAdd (p09Permute permutation x) (p09Permute permutation y) := by
  rfl

/-- The exact remaining FFT computation after the first `k` stages. -/
noncomputable def p09ExactFftCompletion {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (x : ZMod n → ℂ) :
    ZMod n → ℂ :=
  p09Permute plan.finalPermutation
    (p09ApplyExactStageList ((List.ofFn plan.stage).drop k) x)

/-- The local error introduced by rounded stage `i` in one operational run. -/
noncomputable def p09FftStageLocalError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ComplexVecSub (run.stageState (i.val + 1))
    (p09MixedRadixStageApply (plan.stage i) (run.stageState i.val))

/-- A local stage error propagated through all later exact FFT stages. -/
noncomputable def p09PropagatedFftStageError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ExactFftCompletion plan (i.val + 1) (p09FftStageLocalError run i)

/-- The rounded block output at stage `i`, before the optional twiddle. -/
noncomputable def p09FftStageRoundedBlock {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09RoundedMixedRadixBlockApply model (plan.stage i) (run.stageState i.val)

/-- The block-Fourier contribution in equation `(3.6)`, before exact
application of the stage twiddle. -/
noncomputable def p09FftStageBlockLocalError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ComplexVecSub (p09FftStageRoundedBlock run i)
    (p09MixedRadixBlockApply (plan.stage i) (run.stageState i.val))

/-- The separately evaluated twiddle contribution in equation `(3.6)`. -/
noncomputable def p09FftStageTwiddleLocalError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ComplexVecSub
    (p09RoundedMixedRadixTwiddleApply model (plan.stage i)
      (p09FftStageRoundedBlock run i))
    (p09MixedRadixTwiddleApply (plan.stage i)
      (p09FftStageRoundedBlock run i))

/-- The block error after the exact stage twiddle and all later exact FFT
factors. -/
noncomputable def p09PropagatedFftBlockError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ExactFftCompletion plan (i.val + 1)
    (p09MixedRadixTwiddleApply (plan.stage i)
      (p09FftStageBlockLocalError run i))

/-- The twiddle error after all later exact FFT factors. -/
noncomputable def p09PropagatedFftTwiddleError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    ZMod n → ℂ :=
  p09ExactFftCompletion plan (i.val + 1)
    (p09FftStageTwiddleLocalError run i)

private lemma p09ExactFftCompletion_add {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (x y : ZMod n → ℂ) :
    p09ExactFftCompletion plan k (p09ComplexVecAdd x y) =
      p09ComplexVecAdd (p09ExactFftCompletion plan k x)
        (p09ExactFftCompletion plan k y) := by
  unfold p09ExactFftCompletion
  rw [p09ApplyExactStageList_add, p09Permute_add]

private lemma p09MixedRadixTwiddleApply_sub {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x y : ZMod n → ℂ) :
    p09MixedRadixTwiddleApply stage (p09ComplexVecSub x y) =
      p09ComplexVecSub (p09MixedRadixTwiddleApply stage x)
        (p09MixedRadixTwiddleApply stage y) := by
  funext i
  simp only [p09MixedRadixTwiddleApply, p09ComplexVecSub]
  split_ifs <;> ring

private lemma p09FftStageLocalError_eq_block_add_twiddle
    {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    p09FftStageLocalError run i =
      p09ComplexVecAdd
        (p09MixedRadixTwiddleApply (plan.stage i)
          (p09FftStageBlockLocalError run i))
        (p09FftStageTwiddleLocalError run i) := by
  unfold p09FftStageLocalError p09FftStageBlockLocalError
    p09FftStageTwiddleLocalError p09FftStageRoundedBlock
  rw [run.stage_step i]
  unfold p09RoundedMixedRadixStageApply p09MixedRadixStageApply
  rw [p09MixedRadixTwiddleApply_sub]
  funext j
  simp only [p09ComplexVecAdd, p09ComplexVecSub]
  ring

/-- Equation `(3.6)` after exact propagation: each stage error is the sum of
its block-Fourier and separately evaluated twiddle contributions. -/
theorem p09PropagatedFftStageError_eq_block_add_twiddle
    {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    p09PropagatedFftStageError run i =
      p09ComplexVecAdd (p09PropagatedFftBlockError run i)
        (p09PropagatedFftTwiddleError run i) := by
  unfold p09PropagatedFftStageError p09PropagatedFftBlockError
    p09PropagatedFftTwiddleError
  rw [p09FftStageLocalError_eq_block_add_twiddle,
    p09ExactFftCompletion_add]

lemma p09ExactFftCompletion_step_input {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) (hk : k < plan.stageCount)
    (x : ZMod n → ℂ) :
    p09ExactFftCompletion plan k x =
      p09ExactFftCompletion plan (k + 1)
        (p09MixedRadixStageApply (plan.stage ⟨k, hk⟩) x) := by
  unfold p09ExactFftCompletion
  have hlength : k < (List.ofFn plan.stage).length := by simpa using hk
  rw [List.drop_eq_getElem_cons hlength]
  simp only [p09ApplyExactStageList, List.foldl_cons]
  congr 2
  simp

private lemma p09StageState_eq_exact_add_local {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (i : Fin plan.stageCount) :
    run.stageState (i.val + 1) =
      p09ComplexVecAdd
        (p09MixedRadixStageApply (plan.stage i) (run.stageState i.val))
        (p09FftStageLocalError run i) := by
  funext j
  simp [p09FftStageLocalError, p09ComplexVecAdd, p09ComplexVecSub]

lemma p09ExactFftCompletion_run_step {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ)
    (hk : k < plan.stageCount) :
    p09ExactFftCompletion plan (k + 1) (run.stageState (k + 1)) =
      p09ComplexVecAdd
        (p09ExactFftCompletion plan k (run.stageState k))
        (p09PropagatedFftStageError run ⟨k, hk⟩) := by
  let i : Fin plan.stageCount := ⟨k, hk⟩
  rw [p09StageState_eq_exact_add_local run i, p09ExactFftCompletion_add]
  change p09ComplexVecAdd
      (p09ExactFftCompletion plan (k + 1)
        (p09MixedRadixStageApply (plan.stage i) (run.stageState k)))
      (p09PropagatedFftStageError run i) = _
  rw [← p09ExactFftCompletion_step_input plan k hk]

lemma p09ComplexNorm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ComplexVecAdd x y) ≤
      p09ComplexNorm2 x + p09ComplexNorm2 y := by
  let toEuclidean (z : ZMod n → ℂ) :
      EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 z
  have hadd : toEuclidean (p09ComplexVecAdd x y) =
      toEuclidean x + toEuclidean y := by
    ext i
    rfl
  calc
    p09ComplexNorm2 (p09ComplexVecAdd x y) =
        ‖toEuclidean (p09ComplexVecAdd x y)‖ := by
      simp [p09ComplexNorm2, p09ComplexNorm2Sq, toEuclidean,
        EuclideanSpace.norm_eq]
    _ = ‖toEuclidean x + toEuclidean y‖ := by rw [hadd]
    _ ≤ ‖toEuclidean x‖ + ‖toEuclidean y‖ := norm_add_le _ _
    _ = p09ComplexNorm2 x + p09ComplexNorm2 y := by
      simp [p09ComplexNorm2, p09ComplexNorm2Sq, toEuclidean,
        EuclideanSpace.norm_eq]

private lemma p09ComplexRms_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p09ComplexRms (p09ComplexVecAdd x y) ≤
      p09ComplexRms x + p09ComplexRms y := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  unfold p09ComplexRms
  rw [← add_div]
  exact (div_le_div_iff_of_pos_right hsqrt).2 (p09ComplexNorm2_add_le x y)

private noncomputable def p09FftCompletionError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ) : ZMod n → ℂ :=
  p09ComplexVecSub (p09ExactFftCompletion plan k (run.stageState k))
    (p09FourierTransform run.input)

private lemma p09FftCompletionError_zero {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) :
    p09FftCompletionError run 0 = 0 := by
  unfold p09FftCompletionError p09ExactFftCompletion
  rw [run.initial_state]
  change p09ComplexVecSub
      (p09Permute plan.finalPermutation
        (p09ApplyMixedRadixStages plan.stage run.input))
      (p09FourierTransform run.input) = 0
  rw [plan.exact_factorization]
  funext i
  simp [p09ComplexVecSub]

private lemma p09FftCompletionError_step {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ)
    (hk : k < plan.stageCount) :
    p09FftCompletionError run (k + 1) =
      p09ComplexVecAdd (p09FftCompletionError run k)
        (p09PropagatedFftStageError run ⟨k, hk⟩) := by
  unfold p09FftCompletionError
  rw [p09ExactFftCompletion_run_step run k hk]
  funext i
  simp [p09ComplexVecAdd, p09ComplexVecSub]
  ring

private noncomputable def p09StageErrorRmsNat {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ) : ℝ :=
  if hk : k < plan.stageCount then
    p09ComplexRms (p09PropagatedFftStageError run ⟨k, hk⟩)
  else 0

private noncomputable def p09PrefixStageErrorRms {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, p09StageErrorRmsNat run j

private lemma p09PrefixStageErrorRms_succ {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ)
    (hk : k < plan.stageCount) :
    p09PrefixStageErrorRms run (k + 1) =
      p09PrefixStageErrorRms run k +
        p09ComplexRms (p09PropagatedFftStageError run ⟨k, hk⟩) := by
  unfold p09PrefixStageErrorRms
  rw [Finset.sum_range_succ]
  simp [p09StageErrorRmsNat, hk]

private lemma p09FftCompletionErrorRms_le_prefix {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) (k : ℕ)
    (hk : k ≤ plan.stageCount) :
    p09ComplexRms (p09FftCompletionError run k) ≤
      p09PrefixStageErrorRms run k := by
  induction k with
  | zero =>
      rw [p09FftCompletionError_zero]
      simp [p09PrefixStageErrorRms, p09ComplexRms, p09ComplexNorm2,
        p09ComplexNorm2Sq]
  | succ k ih =>
      have hklt : k < plan.stageCount := Nat.lt_of_succ_le hk
      rw [p09FftCompletionError_step run k hklt,
        p09PrefixStageErrorRms_succ run k hklt]
      exact (p09ComplexRms_add_le _ _).trans
        (add_le_add (ih (Nat.le_of_lt hklt)) le_rfl)

lemma p09ExactFftCompletion_final {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ExactFftCompletion plan plan.stageCount x =
      p09Permute plan.finalPermutation x := by
  unfold p09ExactFftCompletion p09ApplyExactStageList
  rw [List.drop_eq_nil_of_le]
  · rfl
  · simp

/-- The global FFT error is bounded by the sum of all propagated local errors. -/
theorem p09FamilyErrorRms_le_stage_sum {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) (ε : P09PositiveEpsilon) :
    p09ComplexRms (p09FamilyFftRoundoffError family ε) ≤
      ∑ i : Fin plan.stageCount,
        p09ComplexRms (p09PropagatedFftStageError (family.run ε) i) := by
  have hbound := p09FftCompletionErrorRms_le_prefix (family.run ε)
    plan.stageCount (Nat.le_refl _)
  have hfinal : p09FftCompletionError (family.run ε) plan.stageCount =
      p09FamilyFftRoundoffError family ε := by
    unfold p09FftCompletionError p09FamilyFftRoundoffError
      p09FftRoundoffError p09FftComputedOutput
    rw [p09ExactFftCompletion_final]
  rw [hfinal] at hbound
  have hsum :
      (∑ i : Fin plan.stageCount,
          p09ComplexRms (p09PropagatedFftStageError (family.run ε) i)) =
        p09PrefixStageErrorRms (family.run ε) plan.stageCount := by
    calc
      (∑ i : Fin plan.stageCount,
          p09ComplexRms (p09PropagatedFftStageError (family.run ε) i)) =
          ∑ i : Fin plan.stageCount,
            p09StageErrorRmsNat (family.run ε) i.val := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [p09StageErrorRmsNat, i.isLt]
      _ = ∑ k ∈ Finset.range plan.stageCount,
            p09StageErrorRmsNat (family.run ε) k :=
        Fin.sum_univ_eq_sum_range _ _
      _ = p09PrefixStageErrorRms (family.run ε) plan.stageCount := rfl
  exact hbound.trans_eq hsum.symm

/-- The first-order contribution of the separately evaluated twiddle in
equation `(3.8)`, after propagation to the original input scale. -/
noncomputable def p09TwiddleFirstOrderBudget {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  if (plan.stage i).useTwiddle then 3 + 2 * γ else 0

/-- The combined first-order contribution of equations `(3.7)` and `(3.8)` at
one mixed-radix stage. -/
noncomputable def p09StageFirstOrderBudget {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  p09Alpha (plan.stage i).radix γ +
    p09TwiddleFirstOrderBudget plan γ i

private lemma p09SumRangeBeforeLast (m : ℕ) (hm : 0 < m) (c : ℝ) :
    (∑ k ∈ Finset.range m, if k + 1 < m then c else 0) =
      ((m : ℝ) - 1) * c := by
  cases m with
  | zero => omega
  | succ m =>
      rw [Finset.sum_range_succ]
      have hsum : (∑ k ∈ Finset.range m,
          if k + 1 < m + 1 then c else 0) = (m : ℝ) * c := by
        calc
          (∑ k ∈ Finset.range m, if k + 1 < m + 1 then c else 0) =
              ∑ _k ∈ Finset.range m, c := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [if_pos]
            exact Nat.succ_lt_succ (Finset.mem_range.1 hk)
          _ = (m : ℝ) * c := by simp
      rw [if_neg (by omega), add_zero, hsum]
      norm_num [Nat.cast_add, Nat.cast_one]

private lemma p09StageFirstOrderBudget_sum {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    (∑ i : Fin plan.stageCount, p09StageFirstOrderBudget plan γ i) =
      p09K plan γ := by
  unfold p09StageFirstOrderBudget p09TwiddleFirstOrderBudget p09K
  rw [Finset.sum_add_distrib]
  congr 1
  let c : ℝ := 3 + 2 * γ
  calc
    (∑ i : Fin plan.stageCount,
        if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
        ∑ i : Fin plan.stageCount,
          if i.val + 1 < plan.stageCount then c else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [plan.twiddle_pattern i]
      simp [c]
    _ = ∑ k ∈ Finset.range plan.stageCount,
          if k + 1 < plan.stageCount then c else 0 :=
      by simpa using
        (Fin.sum_univ_eq_sum_range
          (fun k ↦ if k + 1 < plan.stageCount then c else 0)
          plan.stageCount)
    _ = ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) := by
      simpa [c] using p09SumRangeBeforeLast plan.stageCount
        plan.stageCount_pos c

/-- The separate block and twiddle estimates `(3.7)` and `(3.8)` for one fixed
operational execution family. The error vectors themselves are derived above
from the rounded stage trace and equation `(3.6)`; this record contains only
the two predecessor estimates and their local `O(epsilon^2)` witnesses. -/
structure P09TheoremOneLocalAnalysis {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) where
  blockSecondOrderCoeff : Fin plan.stageCount → ℝ
  block_second_order_nonneg : ∀ i, 0 ≤ blockSecondOrderCoeff i
  twiddleSecondOrderCoeff : Fin plan.stageCount → ℝ
  twiddle_second_order_nonneg : ∀ i, 0 ≤ twiddleSecondOrderCoeff i
  radius : ℝ
  radius_pos : 0 < radius
  block_error_bound : ∀ (ε : P09PositiveEpsilon), ε.1 ≤ radius →
    ∀ i : Fin plan.stageCount,
      p09ComplexRms (p09PropagatedFftBlockError (family.run ε) i) ≤
        ε.1 * Real.sqrt (n : ℝ) *
            p09Alpha (plan.stage i).radix γ *
            p09ComplexRms family.input +
          blockSecondOrderCoeff i * ε.1 ^ 2
  twiddle_error_bound : ∀ (ε : P09PositiveEpsilon), ε.1 ≤ radius →
    ∀ i : Fin plan.stageCount,
      p09ComplexRms (p09PropagatedFftTwiddleError (family.run ε) i) ≤
        ε.1 * Real.sqrt (n : ℝ) *
            p09TwiddleFirstOrderBudget plan γ i *
            p09ComplexRms family.input +
          twiddleSecondOrderCoeff i * ε.1 ^ 2

/-- One fixed source-admissible FFT family together with the local estimates
proved in the paper before Theorem 1. It does not store a global forward or
backward bound. -/
structure P09TheoremOneExecution {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ) where
  family : P09AsymptoticFftFamily plan γ
  localAnalysis : P09TheoremOneLocalAnalysis family

/-- The global second-order coefficient obtained by summing the separate block
and twiddle remainders. -/
noncomputable def p09TheoremOneLocalRemainderSum
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    {family : P09AsymptoticFftFamily plan γ}
    (analysis : P09TheoremOneLocalAnalysis family) : ℝ :=
  ∑ i : Fin plan.stageCount,
    (analysis.blockSecondOrderCoeff i + analysis.twiddleSecondOrderCoeff i)

/-- Equations `(3.6)`--`(3.8)`, propagated through the exact remaining stages,
establish the complete RMS statement of Theorem 1(a). -/
noncomputable def p09TheoremOneRmsAsymptoticOfLocalAnalysis
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (execution : P09TheoremOneExecution plan γ) :
    P09TheoremOneRmsAsymptotic execution.family := by
  let family := execution.family
  let analysis := execution.localAnalysis
  let secondOrderCoeff := p09TheoremOneLocalRemainderSum analysis
  have hcoeff : 0 ≤ secondOrderCoeff :=
    Finset.sum_nonneg fun i _hi ↦
      add_nonneg (analysis.block_second_order_nonneg i)
        (analysis.twiddle_second_order_nonneg i)
  refine
    { secondOrderCoeff := secondOrderCoeff
      secondOrderCoeff_nonneg := hcoeff
      radius := analysis.radius
      radius_pos := analysis.radius_pos
      error_bound := ?_ }
  intro ε hε
  have hstage (i : Fin plan.stageCount) :
      p09ComplexRms (p09PropagatedFftStageError (family.run ε) i) ≤
        ε.1 * Real.sqrt (n : ℝ) *
            p09StageFirstOrderBudget plan γ i *
            p09ComplexRms family.input +
          (analysis.blockSecondOrderCoeff i +
            analysis.twiddleSecondOrderCoeff i) * ε.1 ^ 2 := by
    rw [p09PropagatedFftStageError_eq_block_add_twiddle]
    calc
      p09ComplexRms
          (p09ComplexVecAdd (p09PropagatedFftBlockError (family.run ε) i)
            (p09PropagatedFftTwiddleError (family.run ε) i)) ≤
          p09ComplexRms (p09PropagatedFftBlockError (family.run ε) i) +
            p09ComplexRms (p09PropagatedFftTwiddleError (family.run ε) i) :=
        p09ComplexRms_add_le _ _
      _ ≤ (ε.1 * Real.sqrt (n : ℝ) *
              p09Alpha (plan.stage i).radix γ *
              p09ComplexRms family.input +
            analysis.blockSecondOrderCoeff i * ε.1 ^ 2) +
          (ε.1 * Real.sqrt (n : ℝ) *
              p09TwiddleFirstOrderBudget plan γ i *
              p09ComplexRms family.input +
            analysis.twiddleSecondOrderCoeff i * ε.1 ^ 2) :=
        add_le_add (analysis.block_error_bound ε hε i)
          (analysis.twiddle_error_bound ε hε i)
      _ = ε.1 * Real.sqrt (n : ℝ) *
              p09StageFirstOrderBudget plan γ i *
              p09ComplexRms family.input +
            (analysis.blockSecondOrderCoeff i +
              analysis.twiddleSecondOrderCoeff i) * ε.1 ^ 2 := by
        unfold p09StageFirstOrderBudget
        ring
  calc
    p09ComplexRms (p09FamilyFftRoundoffError family ε) ≤
        ∑ i : Fin plan.stageCount,
          p09ComplexRms (p09PropagatedFftStageError (family.run ε) i) :=
      p09FamilyErrorRms_le_stage_sum family ε
    _ ≤ ∑ i : Fin plan.stageCount,
          (ε.1 * Real.sqrt (n : ℝ) *
                p09StageFirstOrderBudget plan γ i *
                p09ComplexRms family.input +
            (analysis.blockSecondOrderCoeff i +
              analysis.twiddleSecondOrderCoeff i) * ε.1 ^ 2) :=
      Finset.sum_le_sum fun i _hi ↦ hstage i
    _ = ε.1 * Real.sqrt (n : ℝ) *
          (∑ i : Fin plan.stageCount, p09StageFirstOrderBudget plan γ i) *
          p09ComplexRms family.input +
        (∑ i : Fin plan.stageCount,
          (analysis.blockSecondOrderCoeff i +
            analysis.twiddleSecondOrderCoeff i)) * ε.1 ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = ε.1 * Real.sqrt (n : ℝ) * p09K plan γ *
          p09ComplexRms family.input + secondOrderCoeff * ε.1 ^ 2 := by
      rw [p09StageFirstOrderBudget_sum]
      rfl

/-- The imported derivation of Theorem 1(a). It combines the linked
equation-`(3.6)` decomposition with the separate predecessor estimates `(3.7)`
and `(3.8)`; no global forward-error certificate is accepted as input. -/
theorem p09TheoremOneRmsAsymptotic_exists_of_local_analysis
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (execution : P09TheoremOneExecution plan γ) :
    Nonempty (P09TheoremOneRmsAsymptotic execution.family) :=
  ⟨p09TheoremOneRmsAsymptoticOfLocalAnalysis execution⟩

/-! ## Ramos's multidimensional FFT setting -/

/-- One positive multidimensional axis together with the mixed-radix plan used
to evaluate its one-dimensional FFT. -/
structure P09FftAxis where
  order : ℕ
  order_pos : 0 < order
  plan : @P09MixedRadixFftPlan order ⟨Nat.ne_of_gt order_pos⟩

/-- The one-dimensional Theorem 1 constant for a packaged axis. -/
noncomputable def p09AxisK (axis : P09FftAxis) (γ : ℝ) : ℝ :=
  @p09K axis.order ⟨Nat.ne_of_gt axis.order_pos⟩ axis.plan γ

/-- The product index set for an `m`-dimensional array. -/
abbrev P09MultiIndex {m : ℕ} (axis : Fin m → P09FftAxis) :=
  (i : Fin m) → ZMod (axis i).order

noncomputable instance p09MultiIndexFintype {m : ℕ}
    (axis : Fin m → P09FftAxis) : Fintype (P09MultiIndex axis) := by
  letI (i : Fin m) : NeZero (axis i).order :=
    ⟨Nat.ne_of_gt (axis i).order_pos⟩
  infer_instance

/-- Complex arrays on the product of the coordinate index sets. -/
abbrev P09MultiArray {m : ℕ} (axis : Fin m → P09FftAxis) :=
  P09MultiIndex axis → ℂ

/-- The full number `N₁⋯Nₘ` of entries in a multidimensional array. -/
def p09MultiCardinality {m : ℕ} (axis : Fin m → P09FftAxis) : ℕ :=
  ∏ i : Fin m, (axis i).order

/-- Euclidean norm of a complex multidimensional array. -/
noncomputable def p09MultiNorm2 {m : ℕ} {axis : Fin m → P09FftAxis}
    (x : P09MultiArray axis) : ℝ := by
  letI (i : Fin m) : NeZero (axis i).order :=
    ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P09MultiIndex axis))‖

/-- Ramos's RMS norm, normalized by the full product `N₁⋯Nₘ`. -/
noncomputable def p09MultiRms {m : ℕ} {axis : Fin m → P09FftAxis}
    (x : P09MultiArray axis) : ℝ :=
  p09MultiNorm2 x / Real.sqrt (p09MultiCardinality axis : ℝ)

/-- Coordinatewise addition of multidimensional complex arrays. -/
def p09MultiVecAdd {m : ℕ} {axis : Fin m → P09FftAxis}
    (x y : P09MultiArray axis) : P09MultiArray axis :=
  fun index ↦ x index + y index

/-- Coordinatewise subtraction of multidimensional complex arrays. -/
def p09MultiVecSub {m : ℕ} {axis : Fin m → P09FftAxis}
    (x y : P09MultiArray axis) : P09MultiArray axis :=
  fun index ↦ x index - y index

/-- Pointwise sum of a finite family of multidimensional arrays. -/
noncomputable def p09MultiVectorSum {r m : ℕ} {axis : Fin m → P09FftAxis}
    (term : Fin r → P09MultiArray axis) : P09MultiArray axis :=
  fun index ↦ ∑ i : Fin r, term i index

/-- The exact positive-sign one-dimensional DFT in coordinate `i`. -/
noncomputable def p09CoordinateTransform {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (x : P09MultiArray axis) : P09MultiArray axis := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact fun index ↦ ∑ j : ZMod (axis i).order,
    ZMod.stdAddChar (j * index i) * x (Function.update index i j)

/-- Apply the operational one-dimensional FFT to every fiber in coordinate
`i`. The rounded roots, products, and sums are those of
`p09RoundedMixedRadixStageApply`. -/
noncomputable def p09RoundedCoordinateTransform {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : Fin m)
    (model : P09WilkinsonModel) (x : P09MultiArray axis) :
    P09MultiArray axis := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact fun index ↦
    p09RoundedFftApply (axis i).plan model
      (fun j ↦ x (Function.update index i j)) (index i)

/-- A total natural-number interface to the coordinate transform. Values at
indices outside `0,…,m-1` are the identity and are never used by a valid run. -/
noncomputable def p09CoordinateTransformNat {m : ℕ}
    (axis : Fin m → P09FftAxis) (i : ℕ)
    (x : P09MultiArray axis) : P09MultiArray axis :=
  if hi : i < m then p09CoordinateTransform axis ⟨i, hi⟩ x else x

/-- Apply `Tₖ₋₁` first and `T₀` last. Thus prefix `m` is exactly the
nested order `T₁(T₂(⋯(Tₘ X)))` used in Section 4. -/
noncomputable def p09ApplyCoordinatePrefix {m : ℕ}
    (axis : Fin m → P09FftAxis) : ℕ → P09MultiArray axis → P09MultiArray axis
  | 0, x => x
  | i + 1, x =>
      p09ApplyCoordinatePrefix axis i (p09CoordinateTransformNat axis i x)

/-- Product of the first `k` coordinate lengths. -/
def p09PrefixOrderProduct {m : ℕ} (axis : Fin m → P09FftAxis)
    (k : ℕ) (hk : k ≤ m) : ℕ :=
  ∏ i : Fin k, (axis (Fin.castLE hk i)).order

/-- The multidimensional transform plan, including equation `(4.4)` iterated
over every valid prefix of coordinate transforms. -/
structure P09MultidimensionalFftPlan (m : ℕ) [NeZero m] where
  axis : Fin m → P09FftAxis
  prefix_rms_scaling : ∀ (k : ℕ) (hk : k ≤ m) (x : P09MultiArray axis),
    p09MultiRms (p09ApplyCoordinatePrefix axis k x) =
      Real.sqrt (p09PrefixOrderProduct axis k hk : ℝ) * p09MultiRms x

/-- A nested multidimensional FFT execution. `computedState m` is the exactly
represented input, and every preceding state is generated by the rounded
mixed-radix operations for one coordinate. -/
structure P09MultidimensionalFftRun {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (model : P09WilkinsonModel) where
  input : P09MultiArray plan.axis
  computedState : Fin (m + 1) → P09MultiArray plan.axis
  input_exact : ∀ index, model.flInput (input index) = input index
  computed_input : computedState (Fin.last m) = input
  stage_step : ∀ i : Fin m,
    computedState i.castSucc =
      p09RoundedCoordinateTransform plan.axis i model
        (computedState i.succ)

/-- The error introduced by the operational coordinate-`i` computation. It is
derived from the execution trace rather than supplied as a certificate. -/
noncomputable def p09AxisLocalError {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (i : Fin m) :
    P09MultiArray plan.axis :=
  p09MultiVecSub (run.computedState i.castSucc)
    (p09CoordinateTransform plan.axis i (run.computedState i.succ))

/-- The exact output `Y=T₁⋯TₘX`. -/
noncomputable def p09MultiExactOutput {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) : P09MultiArray plan.axis :=
  p09ApplyCoordinatePrefix plan.axis m run.input

/-- The result of the linked nested floating-point execution. -/
def p09MultiComputedOutput {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) : P09MultiArray plan.axis :=
  run.computedState 0

/-- The exact multidimensional output roundoff error `fl(Y)-Y`. -/
noncomputable def p09MultiFftRoundoffError {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) : P09MultiArray plan.axis :=
  p09MultiVecSub (p09MultiComputedOutput run) (p09MultiExactOutput run)

/-- The local error from coordinate `i`, propagated through `T₁,…,Tᵢ₋₁`. -/
noncomputable def p09PropagatedAxisError {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (i : Fin m) :
    P09MultiArray plan.axis :=
  p09ApplyCoordinatePrefix plan.axis i.val (p09AxisLocalError run i)

/-- The scale multiplying `K(Nᵢ,γ)` after propagating coordinate `i`'s
one-dimensional Theorem 1 estimate through the preceding exact transforms. -/
noncomputable def p09PropagatedStageInputRms {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (i : Fin m) : ℝ :=
  p09MultiRms
    (p09ApplyCoordinatePrefix plan.axis (i.val + 1)
      (run.computedState i.succ))

/-- A family of operational multidimensional FFT executions as machine
precision tends to zero. The plan, trigonometric constant, and exactly
represented input are fixed before `epsilon`; only the arithmetic model and
the resulting trace vary. -/
structure P09AsymptoticMultidimensionalFftFamily {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (γ : ℝ) where
  gamma_nonneg : 0 ≤ γ
  input : P09MultiArray plan.axis
  model : P09PositiveEpsilon → P09WilkinsonModel
  model_epsilon : ∀ ε, (model ε).epsilon = ε.1
  model_gamma : ∀ ε, (model ε).gamma = γ
  run : ∀ ε, P09MultidimensionalFftRun plan (model ε)
  run_input : ∀ ε, (run ε).input = input

/-- The fixed exact multidimensional output of an asymptotic execution
family. -/
noncomputable def p09FamilyMultiExactOutput {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {γ : ℝ}
    (family : P09AsymptoticMultidimensionalFftFamily plan γ) :
    P09MultiArray plan.axis :=
  p09ApplyCoordinatePrefix plan.axis m family.input

/-- The output roundoff error at one positive precision in a multidimensional
execution family. -/
noncomputable def p09FamilyMultiFftRoundoffError {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {γ : ℝ}
    (family : P09AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P09PositiveEpsilon) : P09MultiArray plan.axis :=
  p09MultiVecSub (p09MultiComputedOutput (family.run ε))
    (p09FamilyMultiExactOutput family)

/-- Uniform applications of the one-dimensional Theorem 1 estimate to every
coordinate in an operational multidimensional family. Equation `(4.4)` has
already propagated each local estimate through the preceding exact coordinate
transforms. No intermediate-state or final multidimensional estimate is a
field of this structure. -/
structure P09TheoremTwoLocalAsymptotic {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {γ : ℝ}
    (family : P09AsymptoticMultidimensionalFftFamily plan γ) where
  localSecondOrderCoeff : Fin m → ℝ
  local_second_order_nonneg : ∀ i, 0 ≤ localSecondOrderCoeff i
  radius : ℝ
  radius_pos : 0 < radius
  local_error_bound : ∀ (ε : P09PositiveEpsilon), ε.1 ≤ radius →
    ∀ i : Fin m,
      p09MultiRms (p09PropagatedAxisError (family.run ε) i) ≤
        ε.1 * p09AxisK (plan.axis i) γ *
            p09PropagatedStageInputRms (family.run ε) i +
          localSecondOrderCoeff i * ε.1 ^ 2

/-- Sum of the uniform propagated local second-order coefficients. -/
noncomputable def p09TheoremTwoLocalRemainderSum {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {γ : ℝ}
    {family : P09AsymptoticMultidimensionalFftFamily plan γ}
    (axisBounds : P09TheoremTwoLocalAsymptotic family) : ℝ :=
  ∑ i : Fin m, axisBounds.localSecondOrderCoeff i

end HighamBench
```

### `HighamBench.P09TheoremOne`

Path: `paper_bencmark/highambench/shared/HighamBench/P09TheoremOne.lean`
SHA-256: `4b062e6187fec89a2fc1994e3eedc4527fc02c440ed5f474d9409418f09262a5`

```lean
import HighamBench.P09Base

namespace HighamBench

open scoped BigOperators

private lemma p09_abs_flAdd_sub_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hadd⟩ := model.add_model a b
  rw [hadd]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * (1 + θa * model.epsilon) +
          b * (1 + θb * model.epsilon) - (a + b)| =
        model.epsilon * |a * θa + b * θb| := by
      rw [show a * (1 + θa * model.epsilon) +
          b * (1 + θb * model.epsilon) - (a + b) =
            model.epsilon * (a * θa + b * θb) by ring]
      rw [abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * (|a * θa| + |b * θb|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hε
    _ ≤ model.epsilon * (|a| + |b|) := by
      apply mul_le_mul_of_nonneg_left _ hε
      rw [abs_mul, abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg b]

private lemma p09_abs_flMul_sub_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * |a * b| := by
  obtain ⟨θ, hθ, hmul⟩ := model.mul_model a b
  rw [hmul]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        model.epsilon * |a * b| * |θ| := by
      rw [show a * b * (1 + θ * model.epsilon) - a * b =
          model.epsilon * (a * b) * θ by ring]
      rw [abs_mul, abs_mul, abs_of_nonneg hε]
    _ ≤ model.epsilon * |a * b| := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hθ
          (mul_nonneg hε (abs_nonneg (a * b))))

private lemma p09_abs_flSin_sub_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flSin a - Real.sin a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hsin⟩ := model.sin_model a
  rw [hsin]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.sin a + model.gamma * θ * model.epsilon - Real.sin a =
      model.gamma * model.epsilon * θ by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_nonneg hε]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hθ
      (mul_nonneg model.gamma_nonneg hε))

private lemma p09_abs_flCos_sub_le (model : P09WilkinsonModel) (a : ℝ) :
    |model.flCos a - Real.cos a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hcos⟩ := model.cos_model a
  rw [hcos]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [show Real.cos a + model.gamma * θ * model.epsilon - Real.cos a =
      model.gamma * model.epsilon * θ by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_nonneg hε]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hθ
      (mul_nonneg model.gamma_nonneg hε))

private lemma p09_complex_norm_le_of_component_bounds
    (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) :
    ‖z‖ ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have hre_sq : z.re ^ 2 ≤ a ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg ha] using hre
  have him_sq : z.im ^ 2 ≤ b ^ 2 := by
    rw [sq_le_sq]
    simpa only [abs_of_nonneg hb] using him
  exact add_le_add hre_sq him_sq

private lemma p09_complex_norm_le_mk_of_component_bounds
    (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hre : |z.re| ≤ a) (him : |z.im| ≤ b) :
    ‖z‖ ≤ ‖(⟨a, b⟩ : ℂ)‖ := by
  simpa only [Complex.norm_eq_sqrt_sq_add_sq, Complex.normSq_mk] using
    p09_complex_norm_le_of_component_bounds z ha hb hre him

private noncomputable def p09RoundedComplexAddDev
    (model : P09WilkinsonModel) (x y : ℂ) : ℂ :=
  ⟨model.flAdd x.re y.re, model.flAdd x.im y.im⟩

private lemma p09_norm_abs_components (z : ℂ) :
    ‖(⟨|z.re|, |z.im|⟩ : ℂ)‖ = ‖z‖ := by
  simp only [Complex.norm_eq_sqrt_sq_add_sq]
  congr 2 <;> rw [sq_abs]

private lemma p09_norm_roundedComplexAdd_sub_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexAddDev model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let ax : ℂ := ⟨|x.re|, |x.im|⟩
  let ay : ℂ := ⟨|y.re|, |y.im|⟩
  let bound : ℂ := (model.epsilon : ℂ) * (ax + ay)
  have hbre : bound.re = model.epsilon * (|x.re| + |y.re|) := by
    simp [bound, ax, ay]
  have hbim : bound.im = model.epsilon * (|x.im| + |y.im|) := by
    simp [bound, ax, ay]
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexAddDev model x y - (x + y))
    (mul_nonneg hε (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (mul_nonneg hε (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    (by simpa [p09RoundedComplexAddDev] using
      p09_abs_flAdd_sub_le model x.re y.re)
    (by simpa [p09RoundedComplexAddDev] using
      p09_abs_flAdd_sub_le model x.im y.im)
  rw [← hbre, ← hbim] at hcomponent
  calc
    ‖p09RoundedComplexAddDev model x y - (x + y)‖ ≤ ‖bound‖ := hcomponent
    _ = model.epsilon * ‖ax + ay‖ := by
      change ‖(model.epsilon : ℂ) * (ax + ay)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hε]
    _ ≤ model.epsilon * (‖ax‖ + ‖ay‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le ax ay) hε
    _ = model.epsilon * (‖x‖ + ‖y‖) := by
      rw [show ‖ax‖ = ‖x‖ by exact p09_norm_abs_components x,
        show ‖ay‖ = ‖y‖ by exact p09_norm_abs_components y]

private lemma p09_abs_flMul_le (model : P09WilkinsonModel) (a b : ℝ) :
    |model.flMul a b| ≤ (1 + model.epsilon) * |a * b| := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |model.flMul a b| = |a * b + (model.flMul a b - a * b)| := by ring_nf
    _ ≤ |a * b| + |model.flMul a b - a * b| := abs_add_le _ _
    _ ≤ |a * b| + model.epsilon * |a * b| :=
      add_le_add le_rfl (p09_abs_flMul_sub_le model a b)
    _ = (1 + model.epsilon) * |a * b| := by ring

private lemma p09_complex_product_component_majorant
    (x y : ℂ) :
    ‖(⟨|x.re * y.re| + |x.im * y.im|,
        |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ≤
      Real.sqrt 2 * ‖x‖ * ‖y‖ := by
  let a := |x.re|
  let b := |x.im|
  let c := |y.re|
  let d := |y.im|
  have ha : 0 ≤ a := abs_nonneg _
  have hb : 0 ≤ b := abs_nonneg _
  have hc : 0 ≤ c := abs_nonneg _
  have hd : 0 ≤ d := abs_nonneg _
  have hsq_nonneg : 0 ≤ (2 : ℝ) := by norm_num
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hmajor_sq :
      (a * c + b * d) ^ 2 + (a * d + b * c) ^ 2 ≤
        2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
    nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c)]
  have hsq :
      ‖(⟨|x.re * y.re| + |x.im * y.im|,
          |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ^ 2 ≤
        (Real.sqrt 2 * ‖x‖ * ‖y‖) ^ 2 := by
    have hx : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [a, b, pow_two]
      nlinarith [sq_abs x.re, sq_abs x.im]
    have hy : ‖y‖ ^ 2 = c ^ 2 + d ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [c, d, pow_two]
      nlinarith [sq_abs y.re, sq_abs y.im]
    calc
      ‖(⟨|x.re * y.re| + |x.im * y.im|,
          |x.re * y.im| + |x.im * y.re|⟩ : ℂ)‖ ^ 2 =
          (a * c + b * d) ^ 2 + (a * d + b * c) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_mk]
        simp only [abs_mul, a, b, c, d]
        ring
      _ ≤ 2 * ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := hmajor_sq
      _ = (Real.sqrt 2 * ‖x‖ * ‖y‖) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrt, hx, hy]
        ring
  rw [sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))
      (norm_nonneg y))] at hsq
  exact hsq

private lemma p09_norm_roundedComplexMul_sub_le
    (model : P09WilkinsonModel) (x y : ℂ) :
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let A : ℝ := |x.re * y.re| + |x.im * y.im|
  let B : ℝ := |x.re * y.im| + |x.im * y.re|
  let s : ℝ := 2 * model.epsilon + model.epsilon ^ 2
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs : 0 ≤ s := add_nonneg (mul_nonneg (by norm_num) hε) (sq_nonneg _)
  have hre :
      |(p09RoundedComplexMul model x y - x * y).re| ≤ s * A := by
    let p := model.flMul x.re y.re
    let q := model.flMul x.im y.im
    have hadd := p09_abs_flAdd_sub_le model p (-q)
    have hp := p09_abs_flMul_sub_le model x.re y.re
    have hq := p09_abs_flMul_sub_le model x.im y.im
    have hpabs := p09_abs_flMul_le model x.re y.re
    have hqabs := p09_abs_flMul_le model x.im y.im
    change |model.flAdd p (-q) - (x.re * y.re - x.im * y.im)| ≤ _
    calc
      |model.flAdd p (-q) - (x.re * y.re - x.im * y.im)| =
          |(model.flAdd p (-q) - (p - q)) +
            ((p - q) - (x.re * y.re - x.im * y.im))| := by ring_nf
      _ ≤ |model.flAdd p (-q) - (p - q)| +
          |(p - q) - (x.re * y.re - x.im * y.im)| := abs_add_le _ _
      _ ≤ model.epsilon * (|p| + |-q|) +
          (|p - x.re * y.re| + |q - x.im * y.im|) := by
        apply add_le_add
        · simpa only [sub_eq_add_neg] using hadd
        · rw [show (p - q) - (x.re * y.re - x.im * y.im) =
              (p - x.re * y.re) - (q - x.im * y.im) by ring]
          exact abs_sub (p - x.re * y.re) (q - x.im * y.im)
      _ ≤ model.epsilon *
            ((1 + model.epsilon) * |x.re * y.re| +
              (1 + model.epsilon) * |x.im * y.im|) +
          (model.epsilon * |x.re * y.re| +
            model.epsilon * |x.im * y.im|) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hε
          exact add_le_add hpabs (by simpa only [abs_neg] using hqabs)
        · exact add_le_add hp hq
      _ = s * A := by unfold s A; ring
  have him :
      |(p09RoundedComplexMul model x y - x * y).im| ≤ s * B := by
    let p := model.flMul x.re y.im
    let q := model.flMul x.im y.re
    have hadd := p09_abs_flAdd_sub_le model p q
    have hp := p09_abs_flMul_sub_le model x.re y.im
    have hq := p09_abs_flMul_sub_le model x.im y.re
    have hpabs := p09_abs_flMul_le model x.re y.im
    have hqabs := p09_abs_flMul_le model x.im y.re
    change |model.flAdd p q - (x.re * y.im + x.im * y.re)| ≤ _
    calc
      |model.flAdd p q - (x.re * y.im + x.im * y.re)| =
          |(model.flAdd p q - (p + q)) +
            ((p + q) - (x.re * y.im + x.im * y.re))| := by ring_nf
      _ ≤ |model.flAdd p q - (p + q)| +
          |(p + q) - (x.re * y.im + x.im * y.re)| := abs_add_le _ _
      _ ≤ model.epsilon * (|p| + |q|) +
          (|p - x.re * y.im| + |q - x.im * y.re|) := by
        apply add_le_add
        · exact hadd
        · rw [show (p + q) - (x.re * y.im + x.im * y.re) =
              (p - x.re * y.im) + (q - x.im * y.re) by ring]
          exact abs_add_le _ _
      _ ≤ model.epsilon *
            ((1 + model.epsilon) * |x.re * y.im| +
              (1 + model.epsilon) * |x.im * y.re|) +
          (model.epsilon * |x.re * y.im| +
            model.epsilon * |x.im * y.re|) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hε
          exact add_le_add hpabs hqabs
        · exact add_le_add hp hq
      _ = s * B := by unfold s B; ring
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexMul model x y - x * y)
    (mul_nonneg hs hA) (mul_nonneg hs hB) hre him
  calc
    ‖p09RoundedComplexMul model x y - x * y‖ ≤
        ‖(⟨s * A, s * B⟩ : ℂ)‖ := hcomponent
    _ = s * ‖(⟨A, B⟩ : ℂ)‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
      rw [show (s * A) ^ 2 + (s * B) ^ 2 = s ^ 2 * (A ^ 2 + B ^ 2) by ring,
        Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
    _ ≤ s * (Real.sqrt 2 * ‖x‖ * ‖y‖) := by
      apply mul_le_mul_of_nonneg_left _ hs
      exact p09_complex_product_component_majorant x y
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
      have hsqrt : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      have hsqrt_two : Real.sqrt 2 ≤ 2 := hsqrt.trans (by norm_num)
      have hcoef : s * Real.sqrt 2 ≤
          3 * model.epsilon + 2 * model.epsilon ^ 2 := by
        unfold s
        nlinarith
      calc
        s * (Real.sqrt 2 * ‖x‖ * ‖y‖) =
            (s * Real.sqrt 2) * ‖x‖ * ‖y‖ := by ring
        _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
          gcongr

private noncomputable def p09ExactRootDev {q : ℕ} [NeZero q]
    (j : ZMod q) : ℂ :=
  ⟨Real.cos (p09RootAngle j), Real.sin (p09RootAngle j)⟩

private lemma p09ExactRootDev_eq_stdAddChar {q : ℕ} [NeZero q]
    (j : ZMod q) :
    p09ExactRootDev j = ZMod.stdAddChar j := by
  rw [p09StdAddChar_positive_exp]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hexponent :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p09RootAngle j : ℂ) * Complex.I := by
    unfold p09RootAngle
    push_cast
    field_simp
  rw [hexponent, Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [p09ExactRootDev, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private lemma p09_norm_exactRootDev (q : ℕ) [NeZero q] (j : ZMod q) :
    ‖p09ExactRootDev j‖ = 1 := by
  rw [p09ExactRootDev_eq_stdAddChar]
  simp

private lemma p09_norm_roundedRoot_sub_exact_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j - p09ExactRootDev j‖ ≤
      2 * model.gamma * model.epsilon := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγε : 0 ≤ model.gamma * model.epsilon :=
    mul_nonneg model.gamma_nonneg hε
  have hre :
      |(p09RoundedRoot model j - p09ExactRootDev j).re| ≤
        model.gamma * model.epsilon := by
    simpa [p09RoundedRoot, p09ExactRootDev] using
      p09_abs_flCos_sub_le model (p09RootAngle j)
  have him :
      |(p09RoundedRoot model j - p09ExactRootDev j).im| ≤
        model.gamma * model.epsilon := by
    simpa [p09RoundedRoot, p09ExactRootDev] using
      p09_abs_flSin_sub_le model (p09RootAngle j)
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedRoot model j - p09ExactRootDev j) hγε hγε hre him
  calc
    ‖p09RoundedRoot model j - p09ExactRootDev j‖ ≤
        ‖(⟨model.gamma * model.epsilon,
          model.gamma * model.epsilon⟩ : ℂ)‖ := hcomponent
    _ = Real.sqrt 2 * (model.gamma * model.epsilon) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      rw [show (model.gamma * model.epsilon) ^ 2 +
          (model.gamma * model.epsilon) ^ 2 =
            2 * (model.gamma * model.epsilon) ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hγε]
    _ ≤ 2 * model.gamma * model.epsilon := by
      have hsqrt : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sqrt_nonneg 2]
      nlinarith

private lemma p09_norm_roundedRoot_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) :
    ‖p09RoundedRoot model j‖ ≤
      1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p09RoundedRoot model j‖ =
        ‖p09ExactRootDev j +
          (p09RoundedRoot model j - p09ExactRootDev j)‖ := by ring_nf
    _ ≤ ‖p09ExactRootDev j‖ +
        ‖p09RoundedRoot model j - p09ExactRootDev j‖ := norm_add_le _ _
    _ ≤ 1 + 2 * model.gamma * model.epsilon := by
      rw [p09_norm_exactRootDev]
      gcongr
      exact p09_norm_roundedRoot_sub_exact_le model j

private lemma p09_norm_roundedRootMul_sub_exact_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        p09ExactRootDev j * x‖ ≤
      model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
        (2 + 10 * model.gamma) * model.epsilon ^ 2 * ‖x‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hmul := p09_norm_roundedComplexMul_sub_le model
    (p09RoundedRoot model j) x
  have hroot := p09_norm_roundedRoot_sub_exact_le model j
  have hrootnorm := p09_norm_roundedRoot_le model j
  calc
    ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
        p09ExactRootDev j * x‖ =
        ‖(p09RoundedComplexMul model (p09RoundedRoot model j) x -
            p09RoundedRoot model j * x) +
          (p09RoundedRoot model j - p09ExactRootDev j) * x‖ := by ring_nf
    _ ≤ ‖p09RoundedComplexMul model (p09RoundedRoot model j) x -
            p09RoundedRoot model j * x‖ +
          ‖(p09RoundedRoot model j - p09ExactRootDev j) * x‖ := norm_add_le _ _
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
            ‖p09RoundedRoot model j‖ * ‖x‖ +
          (2 * model.gamma * model.epsilon) * ‖x‖ := by
      rw [norm_mul]
      exact add_le_add hmul
        (mul_le_mul_of_nonneg_right hroot (norm_nonneg x))
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) *
            (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
          (2 * model.gamma * model.epsilon) * ‖x‖ := by
      gcongr
    _ ≤ model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
          (2 + 10 * model.gamma) * model.epsilon ^ 2 * ‖x‖ := by
      have hnonneg :
          0 ≤ 4 * model.gamma * model.epsilon ^ 2 *
            (1 - model.epsilon) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hγ) (sq_nonneg _))
          (sub_nonneg.mpr hεone)
      have hcoef :
          (3 * model.epsilon + 2 * model.epsilon ^ 2) *
              (1 + 2 * model.gamma * model.epsilon) +
            2 * model.gamma * model.epsilon ≤
          model.epsilon * (3 + 2 * model.gamma) +
            (2 + 10 * model.gamma) * model.epsilon ^ 2 := by
        nlinarith
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hcoef) (norm_nonneg x)]

private def p09RecursiveSumSecondOrder : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n : ℝ) + 2 * p09RecursiveSumSecondOrder n

private lemma p09RecursiveSumSecondOrder_nonneg (n : ℕ) :
    0 ≤ p09RecursiveSumSecondOrder n := by
  induction n with
  | zero => simp [p09RecursiveSumSecondOrder]
  | succ n ih =>
      simp only [p09RecursiveSumSecondOrder]
      positivity

private lemma p09_abs_recursiveSum_sub_sum_le
    (model : P09WilkinsonModel) (hεone : model.epsilon ≤ 1) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum model.flAdd n v - ∑ i : Fin n, v i| ≤
        ((n : ℝ) * model.epsilon +
            p09RecursiveSumSecondOrder n * model.epsilon ^ 2) *
          ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        simpa [recursiveSum, p09RecursiveSumSecondOrder] using
          (mul_nonneg hε (abs_nonneg (v 0)))
      · let prefixValues : Fin n → ℝ := fun i ↦ v i.castSucc
        let lastTerm : ℝ := v (Fin.last n)
        let exactPrefix : ℝ := ∑ i : Fin n, prefixValues i
        let absPrefix : ℝ := ∑ i : Fin n, |prefixValues i|
        let roundedPrefix : ℝ := recursiveSum model.flAdd n prefixValues
        let previousBound : ℝ :=
          ((n : ℝ) * model.epsilon +
              p09RecursiveSumSecondOrder n * model.epsilon ^ 2) * absPrefix
        have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
        have habsPrefix : 0 ≤ absPrefix := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        have hpreviousCoeff :
            0 ≤ (n : ℝ) * model.epsilon +
              p09RecursiveSumSecondOrder n * model.epsilon ^ 2 :=
          add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
            (mul_nonneg (p09RecursiveSumSecondOrder_nonneg n) (sq_nonneg _))
        have hpreviousNonneg : 0 ≤ previousBound :=
          mul_nonneg hpreviousCoeff habsPrefix
        have hprevious : |roundedPrefix - exactPrefix| ≤ previousBound := by
          simpa [prefixValues, roundedPrefix, exactPrefix, previousBound, absPrefix]
            using ih prefixValues
        have hexactPrefix : |exactPrefix| ≤ absPrefix := by
          simpa [exactPrefix, absPrefix] using
            (Finset.abs_sum_le_sum_abs (f := prefixValues) Finset.univ)
        have hroundedPrefix : |roundedPrefix| ≤ absPrefix + previousBound := by
          calc
            |roundedPrefix| = |exactPrefix + (roundedPrefix - exactPrefix)| := by ring_nf
            _ ≤ |exactPrefix| + |roundedPrefix - exactPrefix| := abs_add_le _ _
            _ ≤ absPrefix + previousBound := add_le_add hexactPrefix hprevious
        have hadd := p09_abs_flAdd_sub_le model roundedPrefix lastTerm
        rw [recursiveSum, dif_neg hn, Fin.sum_univ_castSucc]
        change |model.flAdd roundedPrefix lastTerm -
            (exactPrefix + lastTerm)| ≤ _
        have hsplit :
            |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| ≤
              model.epsilon * (|roundedPrefix| + |lastTerm|) +
                |roundedPrefix - exactPrefix| := by
          calc
            |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| =
                |(model.flAdd roundedPrefix lastTerm -
                    (roundedPrefix + lastTerm)) +
                  (roundedPrefix - exactPrefix)| := by ring_nf
            _ ≤ |model.flAdd roundedPrefix lastTerm -
                    (roundedPrefix + lastTerm)| +
                  |roundedPrefix - exactPrefix| := abs_add_le _ _
            _ ≤ model.epsilon * (|roundedPrefix| + |lastTerm|) +
                  |roundedPrefix - exactPrefix| := add_le_add hadd le_rfl
        calc
          |model.flAdd roundedPrefix lastTerm - (exactPrefix + lastTerm)| ≤
              model.epsilon * (|roundedPrefix| + |lastTerm|) +
                |roundedPrefix - exactPrefix| := hsplit
          _ ≤ model.epsilon * (absPrefix + previousBound + |lastTerm|) +
                previousBound := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (add_le_add hroundedPrefix le_rfl) hε) hprevious
          _ ≤ (((n + 1 : ℕ) : ℝ) * model.epsilon +
                p09RecursiveSumSecondOrder (n + 1) * model.epsilon ^ 2) *
              (absPrefix + |lastTerm|) := by
            have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
            have hlast : 0 ≤ |lastTerm| := abs_nonneg _
            have hrem := p09RecursiveSumSecondOrder_nonneg n
            have hremainA :
                0 ≤ p09RecursiveSumSecondOrder n * model.epsilon ^ 2 *
                  (1 - model.epsilon) * absPrefix :=
              mul_nonneg
                (mul_nonneg
                  (mul_nonneg hrem (sq_nonneg _)) (sub_nonneg.mpr hεone))
                habsPrefix
            have hlinearLast :
                0 ≤ (n : ℝ) * model.epsilon * |lastTerm| :=
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) hlast
            have hremainderLast :
                0 ≤ ((n : ℝ) + 2 * p09RecursiveSumSecondOrder n) *
                  model.epsilon ^ 2 * |lastTerm| :=
              mul_nonneg
                (mul_nonneg
                  (add_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg (by norm_num) hrem))
                  (sq_nonneg _)) hlast
            dsimp [previousBound]
            simp only [p09RecursiveSumSecondOrder, Nat.cast_add, Nat.cast_one]
            nlinarith
          _ = (((n + 1 : ℕ) : ℝ) * model.epsilon +
                p09RecursiveSumSecondOrder (n + 1) * model.epsilon ^ 2) *
              ∑ i : Fin (n + 1), |v i| := by
            congr 1
            rw [Fin.sum_univ_castSucc]

private lemma p09_norm_roundedComplexSum_sub_sum_le {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      ((q : ℝ) * model.epsilon +
          p09RecursiveSumSecondOrder q * model.epsilon ^ 2) *
        ∑ j : ZMod q, ‖term j‖ := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  let coefficient : ℝ :=
    (q : ℝ) * model.epsilon +
      p09RecursiveSumSecondOrder q * model.epsilon ^ 2
  let reTotal : ℝ := ∑ i : Fin q, |(term (index i)).re|
  let imTotal : ℝ := ∑ i : Fin q, |(term (index i)).im|
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoefficient : 0 ≤ coefficient :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
      (mul_nonneg (p09RecursiveSumSecondOrder_nonneg q) (sq_nonneg _))
  have hre :
      |(p09RoundedComplexSum model term - ∑ j : ZMod q, term j).re| ≤
        coefficient * reTotal := by
    have hsum : (∑ j : ZMod q, term j).re =
        ∑ i : Fin q, (term (index i)).re := by
      rw [show (∑ j : ZMod q, term j).re =
          ∑ j : ZMod q, (term j).re by simp]
      symm
      exact Fintype.sum_equiv index
        (fun i : Fin q ↦ (term (index i)).re)
        (fun j : ZMod q ↦ (term j).re) (fun _ ↦ rfl)
    change |(p09RoundedComplexSum model term).re -
        (∑ j : ZMod q, term j).re| ≤ _
    rw [hsum]
    simpa [p09RoundedComplexSum, index, coefficient, reTotal] using
      p09_abs_recursiveSum_sub_sum_le model hεone q
        (fun i : Fin q ↦ (term (index i)).re)
  have him :
      |(p09RoundedComplexSum model term - ∑ j : ZMod q, term j).im| ≤
        coefficient * imTotal := by
    have hsum : (∑ j : ZMod q, term j).im =
        ∑ i : Fin q, (term (index i)).im := by
      rw [show (∑ j : ZMod q, term j).im =
          ∑ j : ZMod q, (term j).im by simp]
      symm
      exact Fintype.sum_equiv index
        (fun i : Fin q ↦ (term (index i)).im)
        (fun j : ZMod q ↦ (term j).im) (fun _ ↦ rfl)
    change |(p09RoundedComplexSum model term).im -
        (∑ j : ZMod q, term j).im| ≤ _
    rw [hsum]
    simpa [p09RoundedComplexSum, index, coefficient, imTotal] using
      p09_abs_recursiveSum_sub_sum_le model hεone q
        (fun i : Fin q ↦ (term (index i)).im)
  have hcomponent := p09_complex_norm_le_mk_of_component_bounds
    (p09RoundedComplexSum model term - ∑ j : ZMod q, term j)
    (mul_nonneg hcoefficient (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    (mul_nonneg hcoefficient (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
    hre him
  let absTerm : Fin q → ℂ := fun i ↦
    ⟨|(term (index i)).re|, |(term (index i)).im|⟩
  have hmajorant :
      ‖(⟨coefficient * reTotal, coefficient * imTotal⟩ : ℂ)‖ ≤
        coefficient * ∑ j : ZMod q, ‖term j‖ := by
    have hmk :
        (⟨coefficient * reTotal, coefficient * imTotal⟩ : ℂ) =
          (coefficient : ℂ) * ∑ i : Fin q, absTerm i := by
      apply Complex.ext <;>
        simp [absTerm, reTotal, imTotal]
    rw [hmk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcoefficient]
    apply mul_le_mul_of_nonneg_left _ hcoefficient
    calc
      ‖∑ i : Fin q, absTerm i‖ ≤ ∑ i : Fin q, ‖absTerm i‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin q, ‖term (index i)‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact p09_norm_abs_components (term (index i))
      _ = ∑ j : ZMod q, ‖term j‖ := by
        exact Fintype.sum_equiv index
          (fun i : Fin q ↦ ‖term (index i)‖)
          (fun j : ZMod q ↦ ‖term j‖) (fun _ ↦ rfl)
  exact hcomponent.trans hmajorant

private lemma p09_norm_roundedComplexSum_two_sub_sum_le
    (model : P09WilkinsonModel) (term : ZMod 2 → ℂ) :
    ‖p09RoundedComplexSum model term - ∑ j : ZMod 2, term j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖term j‖ := by
  let index : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  have hrounded : p09RoundedComplexSum model term =
      p09RoundedComplexAddDev model (term (index 0)) (term (index 1)) := by
    apply Complex.ext <;>
      simp [p09RoundedComplexSum, p09RoundedComplexAddDev, recursiveSum, index]
  have hexact : (∑ j : ZMod 2, term j) =
      term (index 0) + term (index 1) := by
    calc
      (∑ j : ZMod 2, term j) = ∑ i : Fin 2, term (index i) := by
        symm
        exact Fintype.sum_equiv index
          (fun i : Fin 2 ↦ term (index i)) term (fun _ ↦ rfl)
      _ = term (index 0) + term (index 1) := by
        simp [Fin.sum_univ_two]
  rw [hrounded, hexact]
  calc
    ‖p09RoundedComplexAddDev model (term (index 0)) (term (index 1)) -
        (term (index 0) + term (index 1))‖ ≤
      model.epsilon * (‖term (index 0)‖ + ‖term (index 1)‖) :=
        p09_norm_roundedComplexAdd_sub_le model _ _
    _ = model.epsilon * ∑ j : ZMod 2, ‖term j‖ := by
      congr 1
      calc
        ‖term (index 0)‖ + ‖term (index 1)‖ =
            ∑ i : Fin 2, ‖term (index i)‖ := by simp [Fin.sum_univ_two]
        _ = ∑ j : ZMod 2, ‖term j‖ :=
          Fintype.sum_equiv index
            (fun i : Fin 2 ↦ ‖term (index i)‖)
            (fun j : ZMod 2 ↦ ‖term j‖) (fun _ ↦ rfl)

private lemma p09RadixTwoCoefficientApply_eq (j : ZMod 2) (x : ℂ) :
    p09RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  by_cases hj : j = 0
  · subst j
    simp [p09RadixTwoCoefficientApply]
  · have hjone : j = 1 := by
      fin_cases j
      · contradiction
      · rfl
    rw [hjone]
    simp only [p09RadixTwoCoefficientApply, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    rw [p09StdAddChar_positive_exp]
    have hexponent :
        2 * Real.pi * Complex.I * ((1 : ZMod 2).val : ℂ) /
            ((2 : ℕ) : ℂ) = Real.pi * Complex.I := by
      simp [ZMod.val_one]
      ring
    rw [hexponent, Complex.exp_pi_mul_I, neg_one_mul]

private lemma p09_norm_roundedRadixTwoBlock_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p09RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  let term : ZMod 2 → ℂ := fun j ↦
    p09RadixTwoCoefficientApply (j * k) (x j)
  have hsum := p09_norm_roundedComplexSum_two_sub_sum_le model term
  have hexact : (∑ j : ZMod 2, term j) =
      ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact p09RadixTwoCoefficientApply_eq (j * k) (x j)
  have hnorm : (∑ j : ZMod 2, ‖term j‖) = ∑ j : ZMod 2, ‖x j‖ := by
    apply Finset.sum_congr rfl
    intro j _hj
    unfold term
    rw [p09RadixTwoCoefficientApply_eq]
    simp
  simpa [p09RoundedRadixTwoBlock, term, hexact, hnorm] using hsum

private lemma p09StdAddChar_four_zero :
    ZMod.stdAddChar (0 : ZMod 4) = 1 := by simp

private lemma p09StdAddChar_four_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [p09StdAddChar_positive_exp]
  have hval : (1 : ZMod 4).val = 1 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 1) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((1 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) = (Real.pi / 2 : ℂ) * Complex.I := by
    rw [hval]
    push_cast
    norm_num
    ring
  rw [hexponent, Complex.exp_pi_div_two_mul_I]

private lemma p09StdAddChar_four_two :
    ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  rw [p09StdAddChar_positive_exp]
  have hval : (2 : ZMod 4).val = 2 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 2) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((2 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) = Real.pi * Complex.I := by
    rw [hval]
    push_cast
    ring
  rw [hexponent, Complex.exp_pi_mul_I]

private lemma p09StdAddChar_four_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  rw [p09StdAddChar_positive_exp]
  have hval : (3 : ZMod 4).val = 3 := by
    simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 3) (by norm_num))
  have hexponent :
      2 * Real.pi * Complex.I * ((3 : ZMod 4).val : ℂ) /
          ((4 : ℕ) : ℂ) =
        Real.pi * Complex.I + (Real.pi / 2 : ℂ) * Complex.I := by
    rw [hval]
    push_cast
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_pi_div_two_mul_I]
  ring

private lemma p09RadixFourCoefficientApply_eq (j : ZMod 4) (x : ℂ) :
    p09RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  rcases hj with rfl | rfl | rfl | rfl
  · simp [p09RadixFourCoefficientApply, p09StdAddChar_four_zero]
  · rw [p09StdAddChar_four_one]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (1 : ZMod 4) ≠ 0), if_pos rfl]
    apply Complex.ext <;> simp [p09RadixFourCoefficientApply]
  · rw [p09StdAddChar_four_two]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (2 : ZMod 4) ≠ 0),
      if_neg (by decide : (2 : ZMod 4) ≠ 1), if_pos rfl]
    simp
  · rw [p09StdAddChar_four_three]
    simp only [p09RadixFourCoefficientApply,
      if_neg (by decide : (3 : ZMod 4) ≠ 0),
      if_neg (by decide : (3 : ZMod 4) ≠ 1),
      if_neg (by decide : (3 : ZMod 4) ≠ 2)]
    apply Complex.ext <;> simp [p09RadixFourCoefficientApply]

private noncomputable def p09RoundedBalancedFourSumDev
    (model : P09WilkinsonModel) (term : Fin 4 → ℂ) : ℂ :=
  p09RoundedComplexAddDev model
    (p09RoundedComplexAddDev model (term 0) (term 1))
    (p09RoundedComplexAddDev model (term 2) (term 3))

private lemma p09_norm_roundedBalancedFourSum_sub_sum_le
    (model : P09WilkinsonModel) (term : Fin 4 → ℂ) :
    ‖p09RoundedBalancedFourSumDev model term - ∑ i : Fin 4, term i‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ i : Fin 4, ‖term i‖ := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  let exactLeft : ℂ := term 0 + term 1
  let exactRight : ℂ := term 2 + term 3
  let roundedLeft : ℂ := p09RoundedComplexAddDev model (term 0) (term 1)
  let roundedRight : ℂ := p09RoundedComplexAddDev model (term 2) (term 3)
  let inputL1 : ℝ := ∑ i : Fin 4, ‖term i‖
  have hinputL1 : 0 ≤ inputL1 := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hleft : ‖roundedLeft - exactLeft‖ ≤
      model.epsilon * (‖term 0‖ + ‖term 1‖) := by
    exact p09_norm_roundedComplexAdd_sub_le model _ _
  have hright : ‖roundedRight - exactRight‖ ≤
      model.epsilon * (‖term 2‖ + ‖term 3‖) := by
    exact p09_norm_roundedComplexAdd_sub_le model _ _
  have hpair : ‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖ ≤
      model.epsilon * inputL1 := by
    calc
      ‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖ ≤
          model.epsilon * (‖term 0‖ + ‖term 1‖) +
            model.epsilon * (‖term 2‖ + ‖term 3‖) := add_le_add hleft hright
      _ = model.epsilon * inputL1 := by
        simp [inputL1, Fin.sum_univ_four]
        ring
  have hroundedNorm : ‖roundedLeft‖ + ‖roundedRight‖ ≤
      (1 + model.epsilon) * inputL1 := by
    calc
      ‖roundedLeft‖ + ‖roundedRight‖ =
          ‖exactLeft + (roundedLeft - exactLeft)‖ +
            ‖exactRight + (roundedRight - exactRight)‖ := by ring_nf
      _ ≤ (‖exactLeft‖ + ‖roundedLeft - exactLeft‖) +
            (‖exactRight‖ + ‖roundedRight - exactRight‖) :=
        add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ ≤ ((‖term 0‖ + ‖term 1‖) + ‖roundedLeft - exactLeft‖) +
            ((‖term 2‖ + ‖term 3‖) + ‖roundedRight - exactRight‖) := by
        exact add_le_add
          (add_le_add (norm_add_le _ _) le_rfl)
          (add_le_add (norm_add_le _ _) le_rfl)
      _ = inputL1 +
            (‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖) := by
        simp [inputL1, Fin.sum_univ_four]
        ring
      _ ≤ inputL1 + model.epsilon * inputL1 := add_le_add le_rfl hpair
      _ = (1 + model.epsilon) * inputL1 := by ring
  have hfinal := p09_norm_roundedComplexAdd_sub_le model
    roundedLeft roundedRight
  rw [Fin.sum_univ_four]
  have hsum : term 0 + term 1 + term 2 + term 3 =
      exactLeft + exactRight := by
    dsimp [exactLeft, exactRight]
    ring
  rw [hsum]
  unfold p09RoundedBalancedFourSumDev
  change ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
      (exactLeft + exactRight)‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) * inputL1
  calc
    ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
        (exactLeft + exactRight)‖ =
        ‖(p09RoundedComplexAddDev model roundedLeft roundedRight -
            (roundedLeft + roundedRight)) +
          ((roundedLeft - exactLeft) + (roundedRight - exactRight))‖ := by
      ring_nf
    _ ≤ ‖p09RoundedComplexAddDev model roundedLeft roundedRight -
            (roundedLeft + roundedRight)‖ +
          ‖(roundedLeft - exactLeft) + (roundedRight - exactRight)‖ :=
      norm_add_le _ _
    _ ≤ model.epsilon * (‖roundedLeft‖ + ‖roundedRight‖) +
          (‖roundedLeft - exactLeft‖ + ‖roundedRight - exactRight‖) :=
      add_le_add hfinal (norm_add_le _ _)
    _ ≤ model.epsilon * ((1 + model.epsilon) * inputL1) +
          model.epsilon * inputL1 :=
      add_le_add (mul_le_mul_of_nonneg_left hroundedNorm hε) hpair
    _ = (2 * model.epsilon + model.epsilon ^ 2) * inputL1 := by ring

private noncomputable def p09RoundedRadixFourBlockBalancedDev
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) : ℂ :=
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  p09RoundedBalancedFourSumDev model fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))

private lemma p09_norm_roundedRadixFourBlockBalanced_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlockBalancedDev model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i ↦
    p09RadixFourCoefficientApply (index i * k) (x (index i))
  have h := p09_norm_roundedBalancedFourSum_sub_sum_le model term
  have hexact : (∑ i : Fin 4, term i) =
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j := by
    calc
      (∑ i : Fin 4, term i) =
          ∑ i : Fin 4, ZMod.stdAddChar (index i * k) * x (index i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact p09RadixFourCoefficientApply_eq _ _
      _ = ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j :=
        Fintype.sum_equiv index
          (fun i : Fin 4 ↦ ZMod.stdAddChar (index i * k) * x (index i))
          (fun j : ZMod 4 ↦ ZMod.stdAddChar (j * k) * x j) (fun _ ↦ rfl)
  have hnorm : (∑ i : Fin 4, ‖term i‖) = ∑ j : ZMod 4, ‖x j‖ := by
    calc
      (∑ i : Fin 4, ‖term i‖) = ∑ i : Fin 4, ‖x (index i)‖ := by
        apply Finset.sum_congr rfl
        intro i _hi
        unfold term
        rw [p09RadixFourCoefficientApply_eq]
        simp
      _ = ∑ j : ZMod 4, ‖x j‖ :=
        Fintype.sum_equiv index
          (fun i : Fin 4 ↦ ‖x (index i)‖)
          (fun j : ZMod 4 ↦ ‖x j‖) (fun _ ↦ rfl)
  change ‖p09RoundedBalancedFourSumDev model term -
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) *
      ∑ j : ZMod 4, ‖x j‖
  rw [← hexact, ← hnorm]
  exact h

private lemma p09_norm_roundedRadixFourBlock_sub_exact_le
    (model : P09WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p09RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  simpa [p09RoundedRadixFourBlock,
    p09RoundedRadixFourBlockBalancedDev,
    p09RoundedBalancedFourSumDev, p09RoundedComplexAdd,
    p09RoundedComplexAddDev] using
      p09_norm_roundedRadixFourBlockBalanced_sub_exact_le model x k

private lemma p09ComplexNorm2_block_le_of_coordinate_bound
    {n q blockCount : ℕ} [NeZero n] [NeZero q]
    (reindex : Fin blockCount × ZMod q ≃ ZMod n)
    (x error : ZMod n → ℂ) {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hcoord : ∀ (block : Fin blockCount) (k : ZMod q),
      ‖error (reindex (block, k))‖ ≤
        coefficient * ∑ j : ZMod q, ‖x (reindex (block, j))‖) :
    p09ComplexNorm2 error ≤
      (q : ℝ) * coefficient * p09ComplexNorm2 x := by
  let blockL1 : Fin blockCount → ℝ := fun block ↦
    ∑ j : ZMod q, ‖x (reindex (block, j))‖
  have hblockL1 (block : Fin blockCount) : 0 ≤ blockL1 block :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hblock (block : Fin blockCount) :
      (∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
        ((q : ℝ) * coefficient) ^ 2 *
          ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
    have hcoordSq (k : ZMod q) :
        ‖error (reindex (block, k))‖ ^ 2 ≤
          (coefficient * blockL1 block) ^ 2 := by
      rw [sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hcoefficient (hblockL1 block))]
      exact hcoord block k
    have hL1Sq : (blockL1 block) ^ 2 ≤
        (q : ℝ) * ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
      simpa [blockL1] using
        (sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (ZMod q)))
          (f := fun j : ZMod q ↦ ‖x (reindex (block, j))‖))
    calc
      (∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
          ∑ _k : ZMod q, (coefficient * blockL1 block) ^ 2 :=
        Finset.sum_le_sum fun k _hk ↦ hcoordSq k
      _ = (q : ℝ) * (coefficient * blockL1 block) ^ 2 := by simp
      _ ≤ (q : ℝ) * (coefficient ^ 2 *
            ((q : ℝ) *
              ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2)) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hL1Sq (sq_nonneg coefficient))
          (Nat.cast_nonneg _)
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by ring
  have herrReindex :
      (∑ i : ZMod n, ‖error i‖ ^ 2) =
        ∑ p : Fin blockCount × ZMod q, ‖error (reindex p)‖ ^ 2 := by
    symm
    exact Fintype.sum_equiv reindex
      (fun p : Fin blockCount × ZMod q ↦ ‖error (reindex p)‖ ^ 2)
      (fun i : ZMod n ↦ ‖error i‖ ^ 2) (fun _ ↦ rfl)
  have hxReindex :
      (∑ p : Fin blockCount × ZMod q, ‖x (reindex p)‖ ^ 2) =
        ∑ i : ZMod n, ‖x i‖ ^ 2 :=
    Fintype.sum_equiv reindex
      (fun p : Fin blockCount × ZMod q ↦ ‖x (reindex p)‖ ^ 2)
      (fun i : ZMod n ↦ ‖x i‖ ^ 2) (fun _ ↦ rfl)
  have hsq : p09ComplexNorm2Sq error ≤
      ((q : ℝ) * coefficient) ^ 2 * p09ComplexNorm2Sq x := by
    unfold p09ComplexNorm2Sq
    rw [herrReindex, Fintype.sum_prod_type]
    calc
      (∑ block : Fin blockCount,
          ∑ k : ZMod q, ‖error (reindex (block, k))‖ ^ 2) ≤
          ∑ block : Fin blockCount,
            (((q : ℝ) * coefficient) ^ 2 *
              ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2) :=
        Finset.sum_le_sum fun block _hblock ↦ hblock block
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ block : Fin blockCount,
            ∑ j : ZMod q, ‖x (reindex (block, j))‖ ^ 2 := by
        simp only [← Finset.mul_sum]
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ p : Fin blockCount × ZMod q, ‖x (reindex p)‖ ^ 2 := by
        rw [Fintype.sum_prod_type]
      _ = ((q : ℝ) * coefficient) ^ 2 *
          ∑ i : ZMod n, ‖x i‖ ^ 2 := by rw [hxReindex]
  have hqc : 0 ≤ (q : ℝ) * coefficient :=
    mul_nonneg (Nat.cast_nonneg _) hcoefficient
  unfold p09ComplexNorm2
  calc
    Real.sqrt (p09ComplexNorm2Sq error) ≤
        Real.sqrt (((q : ℝ) * coefficient) ^ 2 *
          p09ComplexNorm2Sq x) := Real.sqrt_le_sqrt hsq
    _ = ((q : ℝ) * coefficient) *
        Real.sqrt (p09ComplexNorm2Sq x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hqc]

private noncomputable def p09GenericBlockSecondOrder (q : ℕ) (γ : ℝ) : ℝ :=
  p09RecursiveSumSecondOrder q + (2 + 10 * γ) +
    ((q : ℝ) + p09RecursiveSumSecondOrder q) *
      ((3 + 2 * γ) + (2 + 10 * γ))

private lemma p09GenericBlockSecondOrder_nonneg (q : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09GenericBlockSecondOrder q γ := by
  unfold p09GenericBlockSecondOrder
  have hC := p09RecursiveSumSecondOrder_nonneg q
  have hB : 0 ≤ 2 + 10 * γ := by linarith
  have hqC : 0 ≤ (q : ℝ) + p09RecursiveSumSecondOrder q :=
    add_nonneg (Nat.cast_nonneg _) hC
  have hAB : 0 ≤ (3 + 2 * γ) + (2 + 10 * γ) := by linarith
  exact add_nonneg (add_nonneg hC hB) (mul_nonneg hqC hAB)

private lemma p09_norm_roundedGenericRadixBlock_sub_exact_le
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hq2 : q ≠ 2)
    (model : P09WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q)
    (hεone : model.epsilon ≤ 1) :
    ‖p09RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 * ((q : ℝ) + model.gamma)) *
          (∑ j : ZMod q, ‖x j‖) +
        p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 *
          (∑ j : ZMod q, ‖x j‖) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hq3 : 3 ≤ q := by omega
  let computedTerm : ZMod q → ℂ := fun j ↦
    p09RoundedComplexMul model (p09RoundedRoot model (j * k)) (x j)
  let exactTerm : ZMod q → ℂ := fun j ↦
    ZMod.stdAddChar (j * k) * x j
  let inputL1 : ℝ := ∑ j : ZMod q, ‖x j‖
  let termFirst : ℝ := 3 + 2 * model.gamma
  let termSecond : ℝ := 2 + 10 * model.gamma
  let termCoefficient : ℝ :=
    model.epsilon * termFirst + termSecond * model.epsilon ^ 2
  let sumCoefficient : ℝ :=
    (q : ℝ) * model.epsilon +
      p09RecursiveSumSecondOrder q * model.epsilon ^ 2
  have hinputL1 : 0 ≤ inputL1 := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have htermFirst : 0 ≤ termFirst := by unfold termFirst; positivity
  have htermSecond : 0 ≤ termSecond := by unfold termSecond; positivity
  have htermCoefficient : 0 ≤ termCoefficient := by
    unfold termCoefficient
    positivity
  have hsumCoefficient : 0 ≤ sumCoefficient := by
    unfold sumCoefficient
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε)
      (mul_nonneg (p09RecursiveSumSecondOrder_nonneg q) (sq_nonneg _))
  have hterm (j : ZMod q) :
      ‖computedTerm j - exactTerm j‖ ≤ termCoefficient * ‖x j‖ := by
    have h := p09_norm_roundedRootMul_sub_exact_le model (j * k) (x j) hεone
    rw [p09ExactRootDev_eq_stdAddChar] at h
    simpa [computedTerm, exactTerm, termCoefficient, termFirst, termSecond,
      add_mul] using h
  have htermSum :
      ‖(∑ j : ZMod q, computedTerm j) - ∑ j : ZMod q, exactTerm j‖ ≤
        termCoefficient * inputL1 := by
    calc
      ‖(∑ j : ZMod q, computedTerm j) - ∑ j : ZMod q, exactTerm j‖ =
          ‖∑ j : ZMod q, (computedTerm j - exactTerm j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j : ZMod q, ‖computedTerm j - exactTerm j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, termCoefficient * ‖x j‖ :=
        Finset.sum_le_sum fun j _hj ↦ hterm j
      _ = termCoefficient * inputL1 := by
        simp only [← Finset.mul_sum]
        rfl
  have hcomputedL1 :
      (∑ j : ZMod q, ‖computedTerm j‖) ≤
        (1 + termCoefficient) * inputL1 := by
    calc
      (∑ j : ZMod q, ‖computedTerm j‖) ≤
          ∑ j : ZMod q, (‖exactTerm j‖ + ‖computedTerm j - exactTerm j‖) := by
        apply Finset.sum_le_sum
        intro j _hj
        calc
          ‖computedTerm j‖ = ‖exactTerm j + (computedTerm j - exactTerm j)‖ := by
            ring_nf
          _ ≤ ‖exactTerm j‖ + ‖computedTerm j - exactTerm j‖ := norm_add_le _ _
      _ ≤ ∑ j : ZMod q, (‖x j‖ + termCoefficient * ‖x j‖) := by
        apply Finset.sum_le_sum
        intro j _hj
        rw [show ‖exactTerm j‖ = ‖x j‖ by
          simp [exactTerm]]
        exact add_le_add le_rfl (hterm j)
      _ = (1 + termCoefficient) * inputL1 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        unfold inputL1
        ring
  have hsumRound :
      ‖p09RoundedComplexSum model computedTerm -
          ∑ j : ZMod q, computedTerm j‖ ≤
        sumCoefficient * ∑ j : ZMod q, ‖computedTerm j‖ := by
    simpa [sumCoefficient] using
      p09_norm_roundedComplexSum_sub_sum_le model computedTerm hεone
  have hcombined :
      ‖p09RoundedComplexSum model computedTerm - ∑ j : ZMod q, exactTerm j‖ ≤
        (sumCoefficient * (1 + termCoefficient) + termCoefficient) * inputL1 := by
    calc
      ‖p09RoundedComplexSum model computedTerm -
          ∑ j : ZMod q, exactTerm j‖ =
          ‖(p09RoundedComplexSum model computedTerm -
              ∑ j : ZMod q, computedTerm j) +
            ((∑ j : ZMod q, computedTerm j) -
              ∑ j : ZMod q, exactTerm j)‖ := by ring_nf
      _ ≤ ‖p09RoundedComplexSum model computedTerm -
              ∑ j : ZMod q, computedTerm j‖ +
            ‖(∑ j : ZMod q, computedTerm j) -
              ∑ j : ZMod q, exactTerm j‖ := norm_add_le _ _
      _ ≤ sumCoefficient * (∑ j : ZMod q, ‖computedTerm j‖) +
            termCoefficient * inputL1 := add_le_add hsumRound htermSum
      _ ≤ sumCoefficient * ((1 + termCoefficient) * inputL1) +
            termCoefficient * inputL1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcomputedL1 hsumCoefficient) le_rfl
      _ = (sumCoefficient * (1 + termCoefficient) + termCoefficient) *
            inputL1 := by ring
  have hepssq_le : model.epsilon ^ 2 ≤ model.epsilon := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hεone)]
  have hsumLinear : sumCoefficient ≤
      model.epsilon * ((q : ℝ) + p09RecursiveSumSecondOrder q) := by
    unfold sumCoefficient
    have hC := p09RecursiveSumSecondOrder_nonneg q
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hepssq_le)]
  have htermLinear : termCoefficient ≤
      model.epsilon * (termFirst + termSecond) := by
    unfold termCoefficient
    nlinarith [mul_nonneg htermSecond (sub_nonneg.mpr hepssq_le)]
  have hproduct : sumCoefficient * termCoefficient ≤
      model.epsilon ^ 2 *
        (((q : ℝ) + p09RecursiveSumSecondOrder q) *
          (termFirst + termSecond)) := by
    calc
      sumCoefficient * termCoefficient ≤
          (model.epsilon * ((q : ℝ) + p09RecursiveSumSecondOrder q)) *
            (model.epsilon * (termFirst + termSecond)) := by
        exact mul_le_mul hsumLinear htermLinear htermCoefficient
          (mul_nonneg hε
            (add_nonneg (Nat.cast_nonneg _)
              (p09RecursiveSumSecondOrder_nonneg q)))
      _ = model.epsilon ^ 2 *
          (((q : ℝ) + p09RecursiveSumSecondOrder q) *
            (termFirst + termSecond)) := by ring
  have hcoefficient :
      sumCoefficient * (1 + termCoefficient) + termCoefficient ≤
        model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
          p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 := by
    have hfirst : (q : ℝ) + termFirst ≤ 2 * ((q : ℝ) + model.gamma) := by
      unfold termFirst
      have hq3r : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      linarith
    unfold sumCoefficient termCoefficient p09GenericBlockSecondOrder at *
    nlinarith
  change ‖p09RoundedComplexSum model computedTerm -
      ∑ j : ZMod q, exactTerm j‖ ≤ _
  calc
    ‖p09RoundedComplexSum model computedTerm -
        ∑ j : ZMod q, exactTerm j‖ ≤
        (sumCoefficient * (1 + termCoefficient) + termCoefficient) *
          inputL1 := hcombined
    _ ≤ (model.epsilon * (2 * ((q : ℝ) + model.gamma)) +
          p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2) *
          inputL1 := mul_le_mul_of_nonneg_right hcoefficient hinputL1
    _ = model.epsilon * (2 * ((q : ℝ) + model.gamma)) * inputL1 +
        p09GenericBlockSecondOrder q model.gamma * model.epsilon ^ 2 *
          inputL1 := by ring

private noncomputable def p09BlockCoordinateSecondOrder
    (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 0
  else if q = 4 then 1
  else p09GenericBlockSecondOrder q γ

private lemma p09StdAddChar_ringEquivCongr {a b : ℕ} [NeZero a] [NeZero b]
    (h : a = b) (j : ZMod a) :
    ZMod.stdAddChar (ZMod.ringEquivCongr h j) = ZMod.stdAddChar j := by
  subst b
  rw [ZMod.ringEquivCongr_refl_apply]

private lemma p09_ringEquivCongr_apply_eq_transport {a b : ℕ}
    (h : a = b) (j : ZMod a) :
    ZMod.ringEquivCongr h j = h ▸ j := by
  subst b
  rw [ZMod.ringEquivCongr_refl_apply]

private lemma p09_ringEquivCongr_symm_apply_eq_transport {a b : ℕ}
    (h : a = b) (j : ZMod b) :
    (ZMod.ringEquivCongr h).symm j = h.symm ▸ j := by
  rw [ZMod.ringEquivCongr_symm]
  exact p09_ringEquivCongr_apply_eq_transport h.symm j

private lemma p09_block_coordinate_error_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (block : Fin stage.blockCount) (k : ZMod stage.radix)
    (hεone : model.epsilon ≤ 1) :
    ‖(p09RoundedMixedRadixBlockApply model stage x
          (stage.reindex (block, k)) -
        p09MixedRadixBlockApply stage x (stage.reindex (block, k)))‖ ≤
      (model.epsilon *
          (if stage.radix = 2 then 1
            else if stage.radix = 4 then 2
            else 2 * ((stage.radix : ℝ) + model.gamma)) +
        p09BlockCoordinateSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2) *
        ∑ j : ZMod stage.radix,
          ‖x (stage.permutation (stage.reindex (block, j)))‖ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  by_cases h2 : stage.radix = 2
  · let e2 : ZMod stage.radix ≃+* ZMod 2 := ZMod.ringEquivCongr h2
    let x2 : ZMod 2 → ℂ := fun j ↦
      permuted (stage.reindex (block, e2.symm j))
    let k2 : ZMod 2 := e2 k
    have h := p09_norm_roundedRadixTwoBlock_sub_exact_le model x2 k2
    have hsumExact :
        (∑ j : ZMod stage.radix,
            ZMod.stdAddChar (j * k) * permuted (stage.reindex (block, j))) =
          ∑ j : ZMod 2, ZMod.stdAddChar (j * k2) * x2 j := by
      apply Fintype.sum_equiv e2.toEquiv
      intro j
      simp [e2, k2, x2, ← map_mul, p09StdAddChar_ringEquivCongr]
    have hsumNorm :
        (∑ j : ZMod stage.radix,
          ‖permuted (stage.reindex (block, j))‖) =
            ∑ j : ZMod 2, ‖x2 j‖ := by
      apply Fintype.sum_equiv e2.toEquiv
      intro j
      simp [e2, x2]
    rw [← hsumExact, ← hsumNorm] at h
    simpa [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
      p09ComplexVecSub, h2, permuted, e2, x2, k2,
      p09BlockCoordinateSecondOrder,
      p09_ringEquivCongr_apply_eq_transport,
      p09_ringEquivCongr_symm_apply_eq_transport] using h
  · by_cases h4 : stage.radix = 4
    · let e4 : ZMod stage.radix ≃+* ZMod 4 := ZMod.ringEquivCongr h4
      let x4 : ZMod 4 → ℂ := fun j ↦
        permuted (stage.reindex (block, e4.symm j))
      let k4 : ZMod 4 := e4 k
      have h := p09_norm_roundedRadixFourBlock_sub_exact_le model x4 k4
      have hsumExact :
          (∑ j : ZMod stage.radix,
              ZMod.stdAddChar (j * k) * permuted (stage.reindex (block, j))) =
            ∑ j : ZMod 4, ZMod.stdAddChar (j * k4) * x4 j := by
        apply Fintype.sum_equiv e4.toEquiv
        intro j
        simp [e4, k4, x4, ← map_mul, p09StdAddChar_ringEquivCongr]
      have hsumNorm :
          (∑ j : ZMod stage.radix,
            ‖permuted (stage.reindex (block, j))‖) =
              ∑ j : ZMod 4, ‖x4 j‖ := by
        apply Fintype.sum_equiv e4.toEquiv
        intro j
        simp [e4, x4]
      rw [← hsumExact, ← hsumNorm] at h
      convert h using 1 <;>
        simp [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
          p09ComplexVecSub, h2, h4, permuted, e4, x4, k4,
          p09BlockCoordinateSecondOrder, add_mul,
          p09_ringEquivCongr_apply_eq_transport,
          p09_ringEquivCongr_symm_apply_eq_transport] <;> ring <;> simp
    · have h := p09_norm_roundedGenericRadixBlock_sub_exact_le
        stage.radix_two_le h2 model
          (fun j ↦ permuted (stage.reindex (block, j))) k hεone
      simpa [p09RoundedMixedRadixBlockApply, p09MixedRadixBlockApply,
        p09ComplexVecSub, h2, h4, permuted,
        p09BlockCoordinateSecondOrder, add_mul] using h

private lemma p09ComplexNorm2_comp_equiv {n : ℕ} [NeZero n]
    (equiv : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (fun i ↦ x (equiv i)) = p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  congr 1
  exact Fintype.sum_equiv equiv
    (fun i : ZMod n ↦ ‖x (equiv i)‖ ^ 2)
    (fun i : ZMod n ↦ ‖x i‖ ^ 2) (fun _ ↦ rfl)

private noncomputable def p09BlockVectorSecondOrder (q : ℕ) (γ : ℝ) : ℝ :=
  (q : ℝ) * p09BlockCoordinateSecondOrder q γ

private lemma p09BlockVectorSecondOrder_nonneg (q : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09BlockVectorSecondOrder q γ := by
  unfold p09BlockVectorSecondOrder p09BlockCoordinateSecondOrder
  split_ifs
  · norm_num
  · norm_num
  · exact mul_nonneg (Nat.cast_nonneg _)
      (p09GenericBlockSecondOrder_nonneg q hγ)

private lemma p09_radix_first_coefficient_le (q : ℕ) (hq : 2 ≤ q)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (q : ℝ) *
        (if q = 2 then 1 else if q = 4 then 2 else 2 * ((q : ℝ) + γ)) ≤
      Real.sqrt (q : ℝ) * p09Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    have hsqrt : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num)
    simp [p09Alpha, hsqrt]
  · by_cases h4 : q = 4
    · subst q
      norm_num [p09Alpha]
    · have hsqrt : Real.sqrt (q : ℝ) * Real.sqrt q = q :=
        Real.mul_self_sqrt (Nat.cast_nonneg _)
      simp only [p09Alpha, if_neg h2, if_neg h4]
      nlinarith [mul_nonneg (Nat.cast_nonneg q)
        (add_nonneg (Nat.cast_nonneg q) hγ)]

private lemma p09_norm_roundedMixedRadixBlock_sub_exact_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2
        (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
          (p09MixedRadixBlockApply stage x)) ≤
      model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 x +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 x := by
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  let coordinateCoefficient : ℝ :=
    model.epsilon *
        (if stage.radix = 2 then 1
          else if stage.radix = 4 then 2
          else 2 * ((stage.radix : ℝ) + model.gamma)) +
      p09BlockCoordinateSecondOrder stage.radix model.gamma * model.epsilon ^ 2
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoordSecond :
      0 ≤ p09BlockCoordinateSecondOrder stage.radix model.gamma := by
    unfold p09BlockCoordinateSecondOrder
    split_ifs
    · norm_num
    · norm_num
    · exact p09GenericBlockSecondOrder_nonneg _ model.gamma_nonneg
  have hfirstCoord :
      0 ≤ (if stage.radix = 2 then 1
        else if stage.radix = 4 then 2
          else 2 * ((stage.radix : ℝ) + model.gamma)) := by
    split_ifs
    · norm_num
    · norm_num
    · exact mul_nonneg (by norm_num)
        (add_nonneg (Nat.cast_nonneg _) model.gamma_nonneg)
  have hcoordinateCoefficient : 0 ≤ coordinateCoefficient :=
    add_nonneg (mul_nonneg hε hfirstCoord)
      (mul_nonneg hcoordSecond (sq_nonneg _))
  have hlift := p09ComplexNorm2_block_le_of_coordinate_bound
    stage.reindex permuted
    (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
      (p09MixedRadixBlockApply stage x))
    hcoordinateCoefficient (fun block k ↦ by
      simpa [permuted, p09ComplexVecSub, coordinateCoefficient] using
        p09_block_coordinate_error_le model stage x block k hεone)
  rw [p09ComplexNorm2_comp_equiv stage.permutation x] at hlift
  have hfirst := p09_radix_first_coefficient_le stage.radix
    stage.radix_two_le model.gamma model.gamma_nonneg
  have hnorm : 0 ≤ p09ComplexNorm2 x := Real.sqrt_nonneg _
  calc
    p09ComplexNorm2
        (p09ComplexVecSub (p09RoundedMixedRadixBlockApply model stage x)
          (p09MixedRadixBlockApply stage x)) ≤
        (stage.radix : ℝ) * coordinateCoefficient * p09ComplexNorm2 x :=
      hlift
    _ = ((stage.radix : ℝ) *
          (if stage.radix = 2 then 1
            else if stage.radix = 4 then 2
            else 2 * ((stage.radix : ℝ) + model.gamma)) * model.epsilon +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2) * p09ComplexNorm2 x := by
      unfold coordinateCoefficient p09BlockVectorSecondOrder
      ring
    _ ≤ (Real.sqrt (stage.radix : ℝ) * p09Alpha stage.radix model.gamma *
            model.epsilon +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2) * p09ComplexNorm2 x := by
      apply mul_le_mul_of_nonneg_right _ hnorm
      exact add_le_add (mul_le_mul_of_nonneg_right hfirst hε) le_rfl
    _ = model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 x +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 x := by ring

private lemma p09ComplexNorm2_permute {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09Permute permutation x) = p09ComplexNorm2 x := by
  exact p09ComplexNorm2_comp_equiv permutation x

private lemma p09ComplexNorm2_exactTwiddle {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09MixedRadixTwiddleApply stage x) =
      p09ComplexNorm2 x := by
  unfold p09ComplexNorm2 p09ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [p09MixedRadixTwiddleApply]
  split_ifs <;> simp

/-- Norm amplification of the exact FFT factors remaining after stage `k`. -/
private noncomputable def p09ExactCompletionScale {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ) : ℝ :=
  ((List.ofFn plan.stage).drop k).foldr
    (fun stage scale ↦ Real.sqrt (stage.radix : ℝ) * scale) 1

private lemma p09ExactCompletionScale_final {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) :
    p09ExactCompletionScale plan plan.stageCount = 1 := by
  unfold p09ExactCompletionScale
  rw [List.drop_eq_nil_of_le]
  · rfl
  · simp

private lemma p09ExactCompletionScale_step {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k < plan.stageCount) :
    p09ExactCompletionScale plan k =
      Real.sqrt ((plan.stage ⟨k, hk⟩).radix : ℝ) *
        p09ExactCompletionScale plan (k + 1) := by
  unfold p09ExactCompletionScale
  have hlength : k < (List.ofFn plan.stage).length := by simpa using hk
  rw [List.drop_eq_getElem_cons hlength]
  simp

private lemma p09ExactCompletionScale_pos {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k ≤ plan.stageCount) :
    0 < p09ExactCompletionScale plan k := by
  induction hk using Nat.decreasingInduction with
  | self => rw [p09ExactCompletionScale_final]; norm_num
  | of_succ k hk ih =>
      rw [p09ExactCompletionScale_step plan k hk]
      exact mul_pos
        (Real.sqrt_pos.2 (Nat.cast_pos.2
          (lt_of_lt_of_le (by norm_num) (plan.stage ⟨k, hk⟩).radix_two_le)))
        ih

private lemma p09ComplexNorm2_exactCompletion {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (k : ℕ)
    (hk : k ≤ plan.stageCount) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09ExactFftCompletion plan k x) =
      p09ExactCompletionScale plan k * p09ComplexNorm2 x := by
  revert x
  induction hk using Nat.decreasingInduction with
  | self =>
      intro x
      rw [p09ExactFftCompletion_final, p09ExactCompletionScale_final,
        p09ComplexNorm2_permute]
      simp
  | of_succ k hk ih =>
      intro x
      rw [p09ExactFftCompletion_step_input plan k hk, ih,
        plan.stage_norm_scaling, p09ExactCompletionScale_step plan k hk]
      ring

private lemma p09ExactFftCompletion_zero {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ExactFftCompletion plan 0 x = p09FourierTransform x := by
  unfold p09ExactFftCompletion p09ApplyExactStageList
  simp only [List.drop_zero]
  simpa [p09ApplyMixedRadixStages] using plan.exact_factorization x

private lemma p09ComplexNorm2_fourier {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p09ComplexNorm2 (p09FourierTransform x) =
      Real.sqrt (n : ℝ) * p09ComplexNorm2 x := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
  have h := plan.fourier_rms_scaling x
  unfold p09ComplexRms at h
  field_simp [hsqrt] at h
  exact h

private lemma p09ComplexNorm2_le_mul_of_coordinate_bound
    {n : ℕ} [NeZero n] (x error : ZMod n → ℂ) {coefficient : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hcoord : ∀ i, ‖error i‖ ≤ coefficient * ‖x i‖) :
    p09ComplexNorm2 error ≤ coefficient * p09ComplexNorm2 x := by
  have hsq : p09ComplexNorm2Sq error ≤
      coefficient ^ 2 * p09ComplexNorm2Sq x := by
    unfold p09ComplexNorm2Sq
    calc
      (∑ i : ZMod n, ‖error i‖ ^ 2) ≤
          ∑ i : ZMod n, (coefficient * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoefficient (norm_nonneg _))]
        exact hcoord i
      _ = coefficient ^ 2 * ∑ i : ZMod n, ‖x i‖ ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
  unfold p09ComplexNorm2
  calc
    Real.sqrt (p09ComplexNorm2Sq error) ≤
        Real.sqrt (coefficient ^ 2 * p09ComplexNorm2Sq x) :=
      Real.sqrt_le_sqrt hsq
    _ = coefficient * Real.sqrt (p09ComplexNorm2Sq x) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hcoefficient]

private noncomputable def p09TwiddleVectorSecondOrder
    {n : ℕ} [NeZero n] (stage : P09MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 2 + 10 * γ else 0

private lemma p09TwiddleVectorSecondOrder_nonneg
    {n : ℕ} [NeZero n] (stage : P09MixedRadixStage n) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    0 ≤ p09TwiddleVectorSecondOrder stage γ := by
  unfold p09TwiddleVectorSecondOrder
  split_ifs
  · positivity
  · norm_num

private lemma p09_norm_roundedMixedRadixTwiddle_sub_exact_le
    {n : ℕ} [NeZero n] (model : P09WilkinsonModel)
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ)
    (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2
        (p09ComplexVecSub
          (p09RoundedMixedRadixTwiddleApply model stage x)
          (p09MixedRadixTwiddleApply stage x)) ≤
      (model.epsilon *
          (if stage.useTwiddle then 3 + 2 * model.gamma else 0) +
        p09TwiddleVectorSecondOrder stage model.gamma * model.epsilon ^ 2) *
        p09ComplexNorm2 x := by
  by_cases htwiddle : stage.useTwiddle = true
  · have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    have hfirst : 0 ≤ 3 + 2 * model.gamma := by
      nlinarith [model.gamma_nonneg]
    have hsecond :
        0 ≤ p09TwiddleVectorSecondOrder stage model.gamma :=
      p09TwiddleVectorSecondOrder_nonneg stage model.gamma_nonneg
    simp only [htwiddle, if_true]
    apply p09ComplexNorm2_le_mul_of_coordinate_bound
      (x := x)
      (error := p09ComplexVecSub
        (p09RoundedMixedRadixTwiddleApply model stage x)
        (p09MixedRadixTwiddleApply stage x))
      (coefficient := model.epsilon * (3 + 2 * model.gamma) +
        p09TwiddleVectorSecondOrder stage model.gamma * model.epsilon ^ 2)
      (add_nonneg (mul_nonneg hε hfirst)
        (mul_nonneg hsecond (sq_nonneg model.epsilon)))
    intro i
    convert p09_norm_roundedRootMul_sub_exact_le model
        (stage.twiddleExponent i) (x i) hεone using 1 <;>
      simp [p09RoundedMixedRadixTwiddleApply,
        p09MixedRadixTwiddleApply, p09ComplexVecSub,
        p09TwiddleVectorSecondOrder, htwiddle,
        p09ExactRootDev_eq_stdAddChar] <;> ring
  · have hfalse : stage.useTwiddle = false := Bool.eq_false_of_not_eq_true htwiddle
    simp [p09RoundedMixedRadixTwiddleApply,
      p09MixedRadixTwiddleApply, p09ComplexVecSub,
      p09TwiddleVectorSecondOrder, hfalse,
      p09ComplexNorm2, p09ComplexNorm2Sq]

private lemma p09Alpha_nonneg (q : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ p09Alpha q γ := by
  unfold p09Alpha
  split_ifs
  · exact Real.sqrt_nonneg _
  · norm_num
  · exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (add_nonneg (Nat.cast_nonneg _) hγ)

private lemma p09TwiddleFirstOrderBudget_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09TwiddleFirstOrderBudget plan γ i := by
  unfold p09TwiddleFirstOrderBudget
  split_ifs
  · nlinarith
  · norm_num

private noncomputable def p09TwiddlePropagatedSecondOrder
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  let first := p09TwiddleFirstOrderBudget plan γ i
  let twiddleSecond := p09TwiddleVectorSecondOrder (plan.stage i) γ
  let alpha := p09Alpha (plan.stage i).radix γ
  let blockSecond := p09BlockVectorSecondOrder (plan.stage i).radix γ
  twiddleSecond + (first + twiddleSecond) * (alpha + blockSecond)

private lemma p09TwiddlePropagatedSecondOrder_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09TwiddlePropagatedSecondOrder plan γ i := by
  unfold p09TwiddlePropagatedSecondOrder
  exact add_nonneg
    (p09TwiddleVectorSecondOrder_nonneg (plan.stage i) hγ)
    (mul_nonneg
      (add_nonneg (p09TwiddleFirstOrderBudget_nonneg plan hγ i)
        (p09TwiddleVectorSecondOrder_nonneg (plan.stage i) hγ))
      (add_nonneg (p09Alpha_nonneg _ hγ)
        (p09BlockVectorSecondOrder_nonneg _ hγ)))

private noncomputable def p09StagePropagatedSecondOrder
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (i : Fin plan.stageCount) : ℝ :=
  p09BlockVectorSecondOrder (plan.stage i).radix γ +
    p09TwiddlePropagatedSecondOrder plan γ i

private lemma p09StagePropagatedSecondOrder_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (i : Fin plan.stageCount) :
    0 ≤ p09StagePropagatedSecondOrder plan γ i :=
  add_nonneg (p09BlockVectorSecondOrder_nonneg _ hγ)
    (p09TwiddlePropagatedSecondOrder_nonneg plan hγ i)

private noncomputable def p09CompletedStateNorm
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (k : ℕ) : ℝ :=
  p09ComplexNorm2 (p09ExactFftCompletion plan k (run.stageState k))

private lemma p09_norm_propagatedFftBlockError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftBlockError run i) ≤
      model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
          p09CompletedStateNorm run i.val +
        p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let localError := p09ComplexVecSub
    (p09RoundedMixedRadixBlockApply model stage state)
    (p09MixedRadixBlockApply stage state)
  have hi : i.val ≤ plan.stageCount := Nat.le_of_lt i.isLt
  have hisucc : i.val + 1 ≤ plan.stageCount := Nat.succ_le_of_lt i.isLt
  have hscaleNonneg : 0 ≤ p09ExactCompletionScale plan (i.val + 1) :=
    (p09ExactCompletionScale_pos plan _ hisucc).le
  have hnormState : 0 ≤ p09ComplexNorm2 state := Real.sqrt_nonneg _
  have hsqrtOne : 1 ≤ Real.sqrt ((plan.stage i).radix : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) stage.radix_two_le)
  have hlocal : p09ComplexNorm2 localError ≤
      model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
        p09BlockVectorSecondOrder stage.radix model.gamma *
          model.epsilon ^ 2 * p09ComplexNorm2 state := by
    exact p09_norm_roundedMixedRadixBlock_sub_exact_le model stage state hεone
  have hshortScale :
      p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 state ≤
        p09ExactCompletionScale plan i.val * p09ComplexNorm2 state := by
    rw [p09ExactCompletionScale_step plan i.val i.isLt]
    apply mul_le_mul_of_nonneg_right _ hnormState
    calc
      p09ExactCompletionScale plan (i.val + 1) =
          1 * p09ExactCompletionScale plan (i.val + 1) := by ring
      _ ≤ Real.sqrt ((plan.stage ⟨i.val, i.isLt⟩).radix : ℝ) *
          p09ExactCompletionScale plan (i.val + 1) := by
        apply mul_le_mul_of_nonneg_right _ hscaleNonneg
        simpa using hsqrtOne
  calc
    p09ComplexNorm2 (p09PropagatedFftBlockError run i) =
        p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 localError := by
      unfold p09PropagatedFftBlockError p09FftStageBlockLocalError
        p09FftStageRoundedBlock localError stage state
      rw [p09ComplexNorm2_exactCompletion plan _ hisucc,
        p09ComplexNorm2_exactTwiddle]
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2 * p09ComplexNorm2 state) :=
      mul_le_mul_of_nonneg_left hlocal hscaleNonneg
    _ = model.epsilon * p09Alpha stage.radix model.gamma *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) +
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
          (p09ExactCompletionScale plan (i.val + 1) * p09ComplexNorm2 state) := by
      rw [p09ExactCompletionScale_step plan i.val i.isLt]
      ring
    _ ≤ model.epsilon * p09Alpha stage.radix model.gamma *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) +
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
          (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hshortScale
          (mul_nonneg
            (p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg)
            (sq_nonneg _)))
    _ = model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
          p09CompletedStateNorm run i.val +
        p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09CompletedStateNorm stage state
      rw [p09ComplexNorm2_exactCompletion plan i.val hi]

private lemma p09_norm_roundedFftStageBlock_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09FftStageRoundedBlock run i) ≤
      Real.sqrt ((plan.stage i).radix : ℝ) *
        (1 + model.epsilon * p09Alpha (plan.stage i).radix model.gamma +
          model.epsilon ^ 2 *
            p09BlockVectorSecondOrder (plan.stage i).radix model.gamma) *
        p09ComplexNorm2 (run.stageState i.val) := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let exactBlock := p09MixedRadixBlockApply stage state
  let localError := p09ComplexVecSub
    (p09RoundedMixedRadixBlockApply model stage state) exactBlock
  have hdecomp : p09FftStageRoundedBlock run i =
      p09ComplexVecAdd exactBlock localError := by
    change p09RoundedMixedRadixBlockApply model stage state =
      p09ComplexVecAdd exactBlock localError
    funext j
    simp [exactBlock, localError, p09ComplexVecAdd, p09ComplexVecSub]
  have hexact : p09ComplexNorm2 exactBlock =
      Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state := by
    have h := plan.stage_norm_scaling i state
    unfold p09MixedRadixStageApply at h
    rw [p09ComplexNorm2_exactTwiddle] at h
    exact h
  have hlocal := p09_norm_roundedMixedRadixBlock_sub_exact_le
    model stage state hεone
  have hsqrtOne : 1 ≤ Real.sqrt (stage.radix : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) stage.radix_two_le)
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hsecond : 0 ≤ p09BlockVectorSecondOrder stage.radix model.gamma :=
    p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg
  rw [hdecomp]
  calc
    p09ComplexNorm2 (p09ComplexVecAdd exactBlock localError) ≤
        p09ComplexNorm2 exactBlock + p09ComplexNorm2 localError :=
      p09ComplexNorm2_add_le _ _
    _ ≤ Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state +
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          p09BlockVectorSecondOrder stage.radix model.gamma *
            model.epsilon ^ 2 * p09ComplexNorm2 state) := by
      rw [hexact]
      exact add_le_add le_rfl hlocal
    _ ≤ Real.sqrt (stage.radix : ℝ) * p09ComplexNorm2 state +
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p09Alpha stage.radix model.gamma * p09ComplexNorm2 state +
          Real.sqrt (stage.radix : ℝ) *
            (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state)) := by
      apply add_le_add le_rfl
      apply add_le_add le_rfl
      calc
        p09BlockVectorSecondOrder stage.radix model.gamma * model.epsilon ^ 2 *
            p09ComplexNorm2 state =
            1 * (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state) := by ring
        _ ≤ Real.sqrt (stage.radix : ℝ) *
            (p09BlockVectorSecondOrder stage.radix model.gamma *
              model.epsilon ^ 2 * p09ComplexNorm2 state) := by
          exact mul_le_mul_of_nonneg_right hsqrtOne
            (mul_nonneg (mul_nonneg hsecond (sq_nonneg _))
              (Real.sqrt_nonneg _))
    _ = Real.sqrt ((plan.stage i).radix : ℝ) *
        (1 + model.epsilon * p09Alpha (plan.stage i).radix model.gamma +
          model.epsilon ^ 2 *
            p09BlockVectorSecondOrder (plan.stage i).radix model.gamma) *
        p09ComplexNorm2 (run.stageState i.val) := by
      unfold stage state
      ring

private lemma p09_norm_propagatedFftTwiddleError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) ≤
      model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09TwiddlePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  let stage := plan.stage i
  let state := run.stageState i.val
  let roundedBlock := p09FftStageRoundedBlock run i
  let first := p09TwiddleFirstOrderBudget plan model.gamma i
  let twiddleSecond := p09TwiddleVectorSecondOrder stage model.gamma
  let alpha := p09Alpha stage.radix model.gamma
  let blockSecond := p09BlockVectorSecondOrder stage.radix model.gamma
  let propagatedSecond := p09TwiddlePropagatedSecondOrder plan model.gamma i
  have hi : i.val ≤ plan.stageCount := Nat.le_of_lt i.isLt
  have hisucc : i.val + 1 ≤ plan.stageCount := Nat.succ_le_of_lt i.isLt
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hεsqone : model.epsilon ^ 2 ≤ 1 := by nlinarith [sq_nonneg model.epsilon]
  have hscale : 0 ≤ p09ExactCompletionScale plan (i.val + 1) :=
    (p09ExactCompletionScale_pos plan _ hisucc).le
  have hstate : 0 ≤ p09ComplexNorm2 state := Real.sqrt_nonneg _
  have hfirst : 0 ≤ first :=
    p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i
  have htwiddleSecond : 0 ≤ twiddleSecond :=
    p09TwiddleVectorSecondOrder_nonneg stage model.gamma_nonneg
  have halpha : 0 ≤ alpha := p09Alpha_nonneg _ model.gamma_nonneg
  have hblockSecond : 0 ≤ blockSecond :=
    p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg
  have hcoefficient : 0 ≤
      model.epsilon * first + twiddleSecond * model.epsilon ^ 2 :=
    add_nonneg (mul_nonneg hε hfirst)
      (mul_nonneg htwiddleSecond (sq_nonneg _))
  have hlocal :
      p09ComplexNorm2 (p09FftStageTwiddleLocalError run i) ≤
        (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          p09ComplexNorm2 roundedBlock := by
    simpa [p09FftStageTwiddleLocalError, roundedBlock, stage, first,
      twiddleSecond, p09TwiddleFirstOrderBudget] using
      p09_norm_roundedMixedRadixTwiddle_sub_exact_le model stage roundedBlock hεone
  have hrounded : p09ComplexNorm2 roundedBlock ≤
      Real.sqrt (stage.radix : ℝ) *
        (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) *
        p09ComplexNorm2 state := by
    simpa [roundedBlock, stage, state, alpha, blockSecond] using
      p09_norm_roundedFftStageBlock_le run i hεone
  have hpoly :
      (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) ≤
        model.epsilon * first + propagatedSecond * model.epsilon ^ 2 := by
    have h₁ : model.epsilon * first * blockSecond ≤
        first * blockSecond := by
      calc
        model.epsilon * first * blockSecond ≤ 1 * first * blockSecond := by
          gcongr
        _ = first * blockSecond := by ring
    have h₂ : model.epsilon * twiddleSecond * alpha ≤
        twiddleSecond * alpha := by
      calc
        model.epsilon * twiddleSecond * alpha ≤
            1 * twiddleSecond * alpha := by gcongr
        _ = twiddleSecond * alpha := by ring
    have h₃ : model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
        twiddleSecond * blockSecond := by
      calc
        model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
            1 * twiddleSecond * blockSecond := by gcongr
        _ = twiddleSecond * blockSecond := by ring
    rw [show (model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) =
        model.epsilon * first + model.epsilon ^ 2 *
          (twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond) by ring]
    apply add_le_add le_rfl
    have hbracket :
        twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond ≤
          propagatedSecond := by
      unfold propagatedSecond p09TwiddlePropagatedSecondOrder
      dsimp only
      nlinarith
    calc
      model.epsilon ^ 2 *
          (twiddleSecond + first * alpha +
            model.epsilon * first * blockSecond +
            model.epsilon * twiddleSecond * alpha +
            model.epsilon ^ 2 * twiddleSecond * blockSecond) ≤
          model.epsilon ^ 2 * propagatedSecond :=
        mul_le_mul_of_nonneg_left hbracket (sq_nonneg _)
      _ = propagatedSecond * model.epsilon ^ 2 := by ring
  calc
    p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) =
        p09ExactCompletionScale plan (i.val + 1) *
          p09ComplexNorm2 (p09FftStageTwiddleLocalError run i) := by
      unfold p09PropagatedFftTwiddleError
      rw [p09ComplexNorm2_exactCompletion plan _ hisucc]
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          p09ComplexNorm2 roundedBlock) :=
      mul_le_mul_of_nonneg_left hlocal hscale
    _ ≤ p09ExactCompletionScale plan (i.val + 1) *
        ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (Real.sqrt (stage.radix : ℝ) *
            (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond) *
            p09ComplexNorm2 state)) := by
      gcongr
    _ = ((model.epsilon * first + twiddleSecond * model.epsilon ^ 2) *
          (1 + model.epsilon * alpha + model.epsilon ^ 2 * blockSecond)) *
        (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      rw [p09ExactCompletionScale_step plan i.val i.isLt]
      ring
    _ ≤ (model.epsilon * first + propagatedSecond * model.epsilon ^ 2) *
        (p09ExactCompletionScale plan i.val * p09ComplexNorm2 state) := by
      exact mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg (p09ExactCompletionScale_pos plan _ hi).le hstate)
    _ = model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09TwiddlePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09CompletedStateNorm first propagatedSecond state
      rw [p09ComplexNorm2_exactCompletion plan i.val hi]
      ring

private lemma p09_norm_propagatedFftStageError_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexNorm2 (p09PropagatedFftStageError run i) ≤
      model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09StagePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
  rw [p09PropagatedFftStageError_eq_block_add_twiddle]
  calc
    p09ComplexNorm2
        (p09ComplexVecAdd (p09PropagatedFftBlockError run i)
          (p09PropagatedFftTwiddleError run i)) ≤
        p09ComplexNorm2 (p09PropagatedFftBlockError run i) +
          p09ComplexNorm2 (p09PropagatedFftTwiddleError run i) :=
      p09ComplexNorm2_add_le _ _
    _ ≤ (model.epsilon * p09Alpha (plan.stage i).radix model.gamma *
            p09CompletedStateNorm run i.val +
          p09BlockVectorSecondOrder (plan.stage i).radix model.gamma *
            model.epsilon ^ 2 * p09CompletedStateNorm run i.val) +
        (model.epsilon * p09TwiddleFirstOrderBudget plan model.gamma i *
            p09CompletedStateNorm run i.val +
          p09TwiddlePropagatedSecondOrder plan model.gamma i *
            model.epsilon ^ 2 * p09CompletedStateNorm run i.val) :=
      add_le_add (p09_norm_propagatedFftBlockError_le run i hεone)
        (p09_norm_propagatedFftTwiddleError_le run i hεone)
    _ = model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
          p09CompletedStateNorm run i.val +
        p09StagePropagatedSecondOrder plan model.gamma i *
          model.epsilon ^ 2 * p09CompletedStateNorm run i.val := by
      unfold p09StageFirstOrderBudget p09StagePropagatedSecondOrder
      ring

private lemma p09CompletedStateNorm_step_le
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09CompletedStateNorm run (i.val + 1) ≤
      (1 + model.epsilon * p09StageFirstOrderBudget plan model.gamma i +
        model.epsilon ^ 2 * p09StagePropagatedSecondOrder plan model.gamma i) *
        p09CompletedStateNorm run i.val := by
  have hstep := p09ExactFftCompletion_run_step run i.val i.isLt
  unfold p09CompletedStateNorm
  rw [hstep]
  calc
    p09ComplexNorm2
        (p09ComplexVecAdd
          (p09ExactFftCompletion plan i.val (run.stageState i.val))
          (p09PropagatedFftStageError run i)) ≤
        p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
          p09ComplexNorm2 (p09PropagatedFftStageError run i) :=
      p09ComplexNorm2_add_le _ _
    _ ≤ p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
        (model.epsilon * p09StageFirstOrderBudget plan model.gamma i *
            p09ComplexNorm2
              (p09ExactFftCompletion plan i.val (run.stageState i.val)) +
          p09StagePropagatedSecondOrder plan model.gamma i *
            model.epsilon ^ 2 *
              p09ComplexNorm2
                (p09ExactFftCompletion plan i.val (run.stageState i.val))) := by
      simpa [p09CompletedStateNorm] using
        (add_le_add_right (p09_norm_propagatedFftStageError_le run i hεone)
          (p09ComplexNorm2
            (p09ExactFftCompletion plan i.val (run.stageState i.val))))
    _ = (1 + model.epsilon * p09StageFirstOrderBudget plan model.gamma i +
          model.epsilon ^ 2 * p09StagePropagatedSecondOrder plan model.gamma i) *
        p09ComplexNorm2
          (p09ExactFftCompletion plan i.val (run.stageState i.val)) := by ring

private noncomputable def p09StageEnvelopeNat
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (k : ℕ) : ℝ :=
  if hk : k < plan.stageCount then
    p09StageFirstOrderBudget plan γ ⟨k, hk⟩ +
      p09StagePropagatedSecondOrder plan γ ⟨k, hk⟩
  else 0

private lemma p09StageEnvelopeNat_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (k : ℕ) :
    0 ≤ p09StageEnvelopeNat plan γ k := by
  unfold p09StageEnvelopeNat
  split_ifs with hk
  · exact add_nonneg
      (add_nonneg (p09Alpha_nonneg _ hγ)
        (p09TwiddleFirstOrderBudget_nonneg plan hγ ⟨k, hk⟩))
      (p09StagePropagatedSecondOrder_nonneg plan hγ ⟨k, hk⟩)
  · norm_num

private noncomputable def p09GrowthEnvelope
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ) :
    ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      p09GrowthEnvelope plan γ k + p09StageEnvelopeNat plan γ k +
        p09GrowthEnvelope plan γ k * p09StageEnvelopeNat plan γ k

private lemma p09GrowthEnvelope_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (k : ℕ) :
    0 ≤ p09GrowthEnvelope plan γ k := by
  induction k with
  | zero => simp [p09GrowthEnvelope]
  | succ k ih =>
      rw [p09GrowthEnvelope]
      exact add_nonneg
        (add_nonneg ih (p09StageEnvelopeNat_nonneg plan hγ k))
        (mul_nonneg ih (p09StageEnvelopeNat_nonneg plan hγ k))

private lemma p09CompletedStateNorm_le_growth
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (hεone : model.epsilon ≤ 1) (k : ℕ) (hk : k ≤ plan.stageCount) :
    p09CompletedStateNorm run k ≤
      Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
        (1 + model.epsilon * p09GrowthEnvelope plan model.gamma k) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  induction k with
  | zero =>
      unfold p09CompletedStateNorm
      rw [run.initial_state, p09ExactFftCompletion_zero plan,
        p09ComplexNorm2_fourier plan]
      simp [p09GrowthEnvelope]
  | succ k ih =>
      have hklt : k < plan.stageCount := Nat.lt_of_succ_le hk
      let i : Fin plan.stageCount := ⟨k, hklt⟩
      let budget := p09StageFirstOrderBudget plan model.gamma i
      let second := p09StagePropagatedSecondOrder plan model.gamma i
      let envelope := p09StageEnvelopeNat plan model.gamma k
      let growth := p09GrowthEnvelope plan model.gamma k
      have hbudget : 0 ≤ budget := by
        unfold budget p09StageFirstOrderBudget
        exact add_nonneg (p09Alpha_nonneg _ model.gamma_nonneg)
          (p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i)
      have hsecond : 0 ≤ second :=
        p09StagePropagatedSecondOrder_nonneg plan model.gamma_nonneg i
      have henvelope : envelope = budget + second := by
        simp [envelope, budget, second, p09StageEnvelopeNat, i, hklt]
      have hgrowth : 0 ≤ growth :=
        p09GrowthEnvelope_nonneg plan model.gamma_nonneg k
      have hbase : 0 ≤
          Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have hfactor : 0 ≤
          1 + model.epsilon * budget + model.epsilon ^ 2 * second := by
        positivity
      have hεsq_le : model.epsilon ^ 2 ≤ model.epsilon := by
        nlinarith [mul_nonneg hε
          (sub_nonneg.mpr hεone)]
      calc
        p09CompletedStateNorm run (k + 1) ≤
            (1 + model.epsilon * budget + model.epsilon ^ 2 * second) *
              p09CompletedStateNorm run k := by
          simpa [i, budget, second] using
            p09CompletedStateNorm_step_le run i hεone
        _ ≤ (1 + model.epsilon * budget + model.epsilon ^ 2 * second) *
            (Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
              (1 + model.epsilon * growth)) := by
          exact mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hklt)) hfactor
        _ ≤ (1 + model.epsilon * envelope) *
            (Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
              (1 + model.epsilon * growth)) := by
          apply mul_le_mul_of_nonneg_right
          · rw [henvelope]
            nlinarith [mul_le_mul_of_nonneg_right hεsq_le hsecond]
          · exact mul_nonneg hbase
              (add_nonneg (by norm_num) (mul_nonneg hε hgrowth))
        _ = Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            ((1 + model.epsilon * envelope) *
              (1 + model.epsilon * growth)) := by ring
        _ ≤ Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            (1 + model.epsilon *
              (growth + envelope + growth * envelope)) := by
          apply mul_le_mul_of_nonneg_left _ hbase
          have hcross : model.epsilon ^ 2 * (growth * envelope) ≤
              model.epsilon * (growth * envelope) :=
            mul_le_mul_of_nonneg_right hεsq_le
              (mul_nonneg hgrowth
                (p09StageEnvelopeNat_nonneg plan model.gamma_nonneg k))
          nlinarith
        _ = Real.sqrt (n : ℝ) * p09ComplexNorm2 run.input *
            (1 + model.epsilon * p09GrowthEnvelope plan model.gamma (k + 1)) := by
          rw [p09GrowthEnvelope]

private lemma p09ComplexRms_local_of_completed_bound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (k : ℕ) (hk : k ≤ plan.stageCount) (error : ZMod n → ℂ)
    (first second : ℝ) (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hεone : model.epsilon ≤ 1)
    (herror : p09ComplexNorm2 error ≤
      model.epsilon * first * p09CompletedStateNorm run k +
        second * model.epsilon ^ 2 * p09CompletedStateNorm run k) :
    p09ComplexRms error ≤
      model.epsilon * Real.sqrt (n : ℝ) * first *
          p09ComplexRms run.input +
        ((first * p09GrowthEnvelope plan model.gamma k +
            second * (1 + p09GrowthEnvelope plan model.gamma k)) *
          p09ComplexNorm2 run.input) * model.epsilon ^ 2 := by
  let growth := p09GrowthEnvelope plan model.gamma k
  let inputNorm := p09ComplexNorm2 run.input
  let base := Real.sqrt (n : ℝ) * inputNorm
  let remainder :=
    (first * growth + second * (1 + growth)) * inputNorm
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hgrowth : 0 ≤ growth :=
    p09GrowthEnvelope_nonneg plan model.gamma_nonneg k
  have hinput : 0 ≤ inputNorm := Real.sqrt_nonneg _
  have hbase : 0 ≤ base := mul_nonneg hsqrt.le hinput
  have hlocalCoefficient :
      0 ≤ model.epsilon * first + second * model.epsilon ^ 2 :=
    add_nonneg (mul_nonneg hε hfirst)
      (mul_nonneg hsecond (sq_nonneg _))
  have hgrowthFactor : 0 ≤ 1 + model.epsilon * growth :=
    add_nonneg (by norm_num) (mul_nonneg hε hgrowth)
  have hεsecondGrowth : model.epsilon * second * growth ≤
      second * growth := by
    calc
      model.epsilon * second * growth ≤ 1 * second * growth := by gcongr
      _ = second * growth := by ring
  have hpoly :
      (model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth) ≤
        model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second * (1 + growth)) := by
    rw [show (model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth) =
        model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second + model.epsilon * second * growth) by ring]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith
  have hgrowthBound := p09CompletedStateNorm_le_growth run hεone k hk
  have hnorm : p09ComplexNorm2 error ≤
      model.epsilon * Real.sqrt (n : ℝ) * first * inputNorm +
        Real.sqrt (n : ℝ) * remainder * model.epsilon ^ 2 := by
    calc
      p09ComplexNorm2 error ≤
          (model.epsilon * first + second * model.epsilon ^ 2) *
            p09CompletedStateNorm run k := by
        calc
          p09ComplexNorm2 error ≤
              model.epsilon * first * p09CompletedStateNorm run k +
                second * model.epsilon ^ 2 * p09CompletedStateNorm run k := herror
          _ = (model.epsilon * first + second * model.epsilon ^ 2) *
              p09CompletedStateNorm run k := by ring
      _ ≤ (model.epsilon * first + second * model.epsilon ^ 2) *
          (base * (1 + model.epsilon * growth)) := by
        simpa [base, growth, inputNorm] using
          mul_le_mul_of_nonneg_left hgrowthBound hlocalCoefficient
      _ = ((model.epsilon * first + second * model.epsilon ^ 2) *
          (1 + model.epsilon * growth)) * base := by ring
      _ ≤ (model.epsilon * first + model.epsilon ^ 2 *
          (first * growth + second * (1 + growth))) * base :=
        mul_le_mul_of_nonneg_right hpoly hbase
      _ = model.epsilon * Real.sqrt (n : ℝ) * first * inputNorm +
          Real.sqrt (n : ℝ) * remainder * model.epsilon ^ 2 := by
        unfold base remainder inputNorm
        ring
  unfold p09ComplexRms
  rw [div_le_iff₀ hsqrt]
  convert hnorm using 1 <;> unfold remainder inputNorm <;>
    field_simp [ne_of_gt hsqrt] <;> ring

private noncomputable def p09PrimitiveBlockSecondOrderCoeff
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (input : ZMod n → ℂ) (i : Fin plan.stageCount) : ℝ :=
  (p09Alpha (plan.stage i).radix γ * p09GrowthEnvelope plan γ i.val +
      p09BlockVectorSecondOrder (plan.stage i).radix γ *
        (1 + p09GrowthEnvelope plan γ i.val)) *
    p09ComplexNorm2 input

private noncomputable def p09PrimitiveTwiddleSecondOrderCoeff
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (input : ZMod n → ℂ) (i : Fin plan.stageCount) : ℝ :=
  (p09TwiddleFirstOrderBudget plan γ i *
        p09GrowthEnvelope plan γ i.val +
      p09TwiddlePropagatedSecondOrder plan γ i *
        (1 + p09GrowthEnvelope plan γ i.val)) *
    p09ComplexNorm2 input

private lemma p09PrimitiveBlockSecondOrderCoeff_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (input : ZMod n → ℂ) (i : Fin plan.stageCount) :
    0 ≤ p09PrimitiveBlockSecondOrderCoeff plan γ input i := by
  unfold p09PrimitiveBlockSecondOrderCoeff
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (p09Alpha_nonneg _ hγ)
        (p09GrowthEnvelope_nonneg plan hγ i.val))
      (mul_nonneg (p09BlockVectorSecondOrder_nonneg _ hγ)
        (add_nonneg (by norm_num)
          (p09GrowthEnvelope_nonneg plan hγ i.val))))
    (Real.sqrt_nonneg _)

private lemma p09PrimitiveTwiddleSecondOrderCoeff_nonneg
    {n : ℕ} [NeZero n] (plan : P09MixedRadixFftPlan n) {γ : ℝ}
    (hγ : 0 ≤ γ) (input : ZMod n → ℂ) (i : Fin plan.stageCount) :
    0 ≤ p09PrimitiveTwiddleSecondOrderCoeff plan γ input i := by
  unfold p09PrimitiveTwiddleSecondOrderCoeff
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (p09TwiddleFirstOrderBudget_nonneg plan hγ i)
        (p09GrowthEnvelope_nonneg plan hγ i.val))
      (mul_nonneg (p09TwiddlePropagatedSecondOrder_nonneg plan hγ i)
        (add_nonneg (by norm_num)
          (p09GrowthEnvelope_nonneg plan hγ i.val))))
    (Real.sqrt_nonneg _)

private lemma p09PrimitiveBlockRmsBound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexRms (p09PropagatedFftBlockError run i) ≤
      model.epsilon * Real.sqrt (n : ℝ) *
          p09Alpha (plan.stage i).radix model.gamma * p09ComplexRms run.input +
        p09PrimitiveBlockSecondOrderCoeff plan model.gamma run.input i *
          model.epsilon ^ 2 := by
  exact p09ComplexRms_local_of_completed_bound run i.val
    (Nat.le_of_lt i.isLt) _
    (p09Alpha (plan.stage i).radix model.gamma)
    (p09BlockVectorSecondOrder (plan.stage i).radix model.gamma)
    (p09Alpha_nonneg _ model.gamma_nonneg)
    (p09BlockVectorSecondOrder_nonneg _ model.gamma_nonneg)
    hεone (p09_norm_propagatedFftBlockError_le run i hεone)

private lemma p09PrimitiveTwiddleRmsBound
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n}
    {model : P09WilkinsonModel} (run : P09MixedRadixFftRun plan model)
    (i : Fin plan.stageCount) (hεone : model.epsilon ≤ 1) :
    p09ComplexRms (p09PropagatedFftTwiddleError run i) ≤
      model.epsilon * Real.sqrt (n : ℝ) *
          p09TwiddleFirstOrderBudget plan model.gamma i * p09ComplexRms run.input +
        p09PrimitiveTwiddleSecondOrderCoeff plan model.gamma run.input i *
          model.epsilon ^ 2 := by
  exact p09ComplexRms_local_of_completed_bound run i.val
    (Nat.le_of_lt i.isLt) _
    (p09TwiddleFirstOrderBudget plan model.gamma i)
    (p09TwiddlePropagatedSecondOrder plan model.gamma i)
    (p09TwiddleFirstOrderBudget_nonneg plan model.gamma_nonneg i)
    (p09TwiddlePropagatedSecondOrder_nonneg plan model.gamma_nonneg i)
    hεone (p09_norm_propagatedFftTwiddleError_le run i hεone)

/-- The paper's local estimates `(3.7)` and `(3.8)`, derived from the scalar
Wilkinson model and the operational mixed-radix kernels. -/
noncomputable def p09PrimitiveTheoremOneLocalAnalysis
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) :
    P09TheoremOneLocalAnalysis family := by
  refine
    { blockSecondOrderCoeff :=
        p09PrimitiveBlockSecondOrderCoeff plan γ family.input
      block_second_order_nonneg := ?_
      twiddleSecondOrderCoeff :=
        p09PrimitiveTwiddleSecondOrderCoeff plan γ family.input
      twiddle_second_order_nonneg := ?_
      radius := 1
      radius_pos := by norm_num
      block_error_bound := ?_
      twiddle_error_bound := ?_ }
  · intro i
    exact p09PrimitiveBlockSecondOrderCoeff_nonneg plan
      family.gamma_nonneg family.input i
  · intro i
    exact p09PrimitiveTwiddleSecondOrderCoeff_nonneg plan
      family.gamma_nonneg family.input i
  · intro ε hε i
    have hmodelEpsilon : (family.model ε).epsilon ≤ 1 := by
      rw [family.model_epsilon ε]
      exact hε
    have h := p09PrimitiveBlockRmsBound (family.run ε) i hmodelEpsilon
    rw [family.model_epsilon ε, family.model_gamma ε,
      family.run_input ε] at h
    exact h
  · intro ε hε i
    have hmodelEpsilon : (family.model ε).epsilon ≤ 1 := by
      rw [family.model_epsilon ε]
      exact hε
    have h := p09PrimitiveTwiddleRmsBound (family.run ε) i hmodelEpsilon
    rw [family.model_epsilon ε, family.model_gamma ε,
      family.run_input ε] at h
    exact h

/-- Theorem 1(a), proved from the operation-level FFT execution family. The
caller supplies no local or global error-bound certificate. -/
theorem p09TheoremOneRmsAsymptotic_exists
    {n : ℕ} [NeZero n] {plan : P09MixedRadixFftPlan n} {γ : ℝ}
    (family : P09AsymptoticFftFamily plan γ) :
    Nonempty (P09TheoremOneRmsAsymptotic family) :=
  p09TheoremOneRmsAsymptotic_exists_of_local_analysis
    { family := family
      localAnalysis := p09PrimitiveTheoremOneLocalAnalysis family }

end HighamBench
```

### `HighamBench.P09Definitions`

Path: `paper_bencmark/highambench/shared/HighamBench/P09Definitions.lean`
SHA-256: `dd89e5c96be1ed020dcaa021111d816613f0151eac62544e7315ae6eac79c332`

```lean
import HighamBench.P09Base
import HighamBench.P09TheoremOne
```
