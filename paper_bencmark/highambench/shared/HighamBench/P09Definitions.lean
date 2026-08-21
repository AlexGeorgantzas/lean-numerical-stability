import HighamBench.Core
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
  ‖x‖

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
  radix_ne_zero : radix ≠ 0
  blockCount : ℕ
  blockCount_ne_zero : blockCount ≠ 0
  order_eq : blockCount * radix = n
  reindex : Fin blockCount × ZMod radix ≃ ZMod n
  permutation : ZMod n ≃ ZMod n
  useTwiddle : Bool
  twiddleExponent : ZMod n → ZMod n

/-- Exact action of one mixed-radix FFT factor. -/
noncomputable def p09MixedRadixStageApply {n : ℕ} [NeZero n]
    (stage : P09MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  let blocked : ZMod n → ℂ := fun i ↦
    let bi := stage.reindex.symm i
    ∑ j : ZMod stage.radix,
      ZMod.stdAddChar (j * bi.2) * permuted (stage.reindex (bi.1, j))
  exact fun i ↦
    if stage.useTwiddle then
      ZMod.stdAddChar (stage.twiddleExponent i) * blocked i
    else blocked i

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

/-- Sequential rounded summation of a complex vector. -/
noncomputable def p09RoundedComplexSum {q : ℕ} [NeZero q]
    (model : P09WilkinsonModel) (term : ZMod q → ℂ) : ℂ :=
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  ⟨recursiveSum model.flAdd q fun i ↦ (term (index i)).re,
    recursiveSum model.flAdd q fun i ↦ (term (index i)).im⟩

/-- One operational mixed-radix FFT stage. It performs the paper's exact
permutation, evaluates each block Fourier sum with rounded trigonometric,
multiplication, and addition operations, and then performs the optional rounded
twiddle multiplication. -/
noncomputable def p09RoundedMixedRadixStageApply {n : ℕ} [NeZero n]
    (model : P09WilkinsonModel) (stage : P09MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  let blocked : ZMod n → ℂ := fun i ↦
    let bi := stage.reindex.symm i
    p09RoundedComplexSum model fun j ↦
      p09RoundedComplexMul model (p09RoundedRoot model (j * bi.2))
        (permuted (stage.reindex (bi.1, j)))
  exact fun i ↦
    if stage.useTwiddle then
      p09RoundedComplexMul model
        (p09RoundedRoot model (stage.twiddleExponent i)) (blocked i)
    else blocked i

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

/-- Theorem 1(a) with the source's `O(epsilon^2)` interpreted uniformly on a
right neighborhood of zero. The coefficient and radius are chosen after the
fixed execution family but before any particular positive `epsilon`. -/
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

/-- A nested multidimensional FFT execution. `computedState m` is `X`, and
`computedState i` is the rounded result after evaluating coordinate `i` on
`computedState (i+1)`. The final field is the exact telescoping identity from
the proof of Theorem 2. -/
structure P09MultidimensionalFftRun {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (model : P09WilkinsonModel) where
  input : P09MultiArray plan.axis
  computedState : Fin (m + 1) → P09MultiArray plan.axis
  localError : Fin m → P09MultiArray plan.axis
  computed_input : computedState (Fin.last m) = input
  stage_step : ∀ i : Fin m,
    computedState i.castSucc =
      p09MultiVecAdd
        (p09CoordinateTransform plan.axis i (computedState i.succ))
        (localError i)
  input_rms_condition :
    p09MultiRms (fun index ↦ model.flInput (input index)) = p09MultiRms input ∨
      ∃ inputFirstOrderCoeff : ℝ,
        0 ≤ inputFirstOrderCoeff ∧
        |p09MultiRms (fun index ↦ model.flInput (input index)) -
            p09MultiRms input| ≤ inputFirstOrderCoeff * model.epsilon
  telescoping_error :
    p09MultiVecSub (computedState 0)
        (p09ApplyCoordinatePrefix plan.axis m input) =
      p09MultiVectorSum fun i ↦
        p09ApplyCoordinatePrefix plan.axis i.val (localError i)

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
  p09ApplyCoordinatePrefix plan.axis i.val (run.localError i)

/-- The scale multiplying `K(Nᵢ,γ)` after propagating coordinate `i`'s
one-dimensional Theorem 1 estimate through the preceding exact transforms. -/
noncomputable def p09PropagatedStageInputRms {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) (i : Fin m) : ℝ :=
  Real.sqrt
      (p09PrefixOrderProduct plan.axis i.val (Nat.le_of_lt i.isLt) : ℝ) *
    Real.sqrt ((plan.axis i).order : ℝ) *
    p09MultiRms (run.computedState i.succ)

/-- Equations `(4.3)` and `(4.4)` with every hidden remainder exposed. The
`intermediate_rms_approx` field includes the paper's exact-or-`O(ε)` input
RMS condition at the last coordinate and the analogous intermediate facts. -/
structure P09TheoremTwoRmsCertificate {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    (run : P09MultidimensionalFftRun plan model) where
  localSecondOrderCoeff : Fin m → ℝ
  intermediateFirstOrderCoeff : Fin m → ℝ
  local_second_order_nonneg : ∀ i, 0 ≤ localSecondOrderCoeff i
  intermediate_first_order_nonneg : ∀ i, 0 ≤ intermediateFirstOrderCoeff i
  local_error_bound : ∀ i : Fin m,
    p09MultiRms (run.localError i) ≤
      model.epsilon * Real.sqrt ((plan.axis i).order : ℝ) *
          p09AxisK (plan.axis i) model.gamma *
          p09MultiRms (run.computedState i.succ) +
        localSecondOrderCoeff i * model.epsilon ^ 2
  intermediate_rms_approx : ∀ i : Fin m,
    |p09PropagatedStageInputRms run i - p09MultiRms (p09MultiExactOutput run)| ≤
      intermediateFirstOrderCoeff i * model.epsilon

/-- The explicit finite coefficient replacing Theorem 2(a)'s final
`O(ε²)` term. -/
noncomputable def p09TheoremTwoRemainderCoeff {m : ℕ} [NeZero m]
    {plan : P09MultidimensionalFftPlan m} {model : P09WilkinsonModel}
    {run : P09MultidimensionalFftRun plan model}
    (certificate : P09TheoremTwoRmsCertificate run) : ℝ :=
  ∑ i : Fin m, (
    Real.sqrt
          (p09PrefixOrderProduct plan.axis i.val (Nat.le_of_lt i.isLt) : ℝ) *
        certificate.localSecondOrderCoeff i +
      p09AxisK (plan.axis i) model.gamma *
        certificate.intermediateFirstOrderCoeff i)

end HighamBench
