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
