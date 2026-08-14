import HighamBench.Core
import Mathlib.Analysis.Fourier.ZMod

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

/-- A stage-level execution trace of the one-dimensional floating-point FFT.
The exact stage action is fixed by the certified factorization; `localError`
is the roundoff introduced while evaluating that stage under `model`. -/
structure P09MixedRadixFftRun {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel) where
  input : ZMod n → ℂ
  computedOutput : ZMod n → ℂ
  stageState : ℕ → ZMod n → ℂ
  localError : Fin plan.stageCount → ZMod n → ℂ
  localSecondOrderCoeff : Fin plan.stageCount → ℝ
  input_exact : ∀ i : ZMod n, model.flInput (input i) = input i
  initial_state : stageState 0 = input
  stage_step : ∀ i : Fin plan.stageCount,
    stageState (i.val + 1) =
      p09ComplexVecAdd
        (p09MixedRadixStageApply (plan.stage i) (stageState i.val))
        (localError i)
  computed_output : computedOutput =
    p09Permute plan.finalPermutation (stageState plan.stageCount)
  local_second_order_nonneg : ∀ i, 0 ≤ localSecondOrderCoeff i
  local_error_bound : ∀ i : Fin plan.stageCount,
    p09ComplexRms (localError i) ≤
      model.epsilon * Real.sqrt ((plan.stage i).radix : ℝ) *
          (p09Alpha (plan.stage i).radix model.gamma +
            if (plan.stage i).useTwiddle then 3 + 2 * model.gamma else 0) *
          p09ComplexRms (stageState i.val) +
        localSecondOrderCoeff i * model.epsilon ^ 2

/-- The exact output roundoff error of a linked FFT execution. -/
noncomputable def p09FftRoundoffError {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) : ZMod n → ℂ :=
  p09ComplexVecSub run.computedOutput (p09FourierTransform run.input)

/-- Theorem 1(a), specialized to the exact-input run and written as an
absolute finite certificate. `secondOrderCoeff * epsilon^2` exposes the
otherwise unquantified `O(epsilon^2)` term. -/
structure P09TheoremOneRmsCertificate {n : ℕ} [NeZero n]
    {plan : P09MixedRadixFftPlan n} {model : P09WilkinsonModel}
    (run : P09MixedRadixFftRun plan model) where
  secondOrderCoeff : ℝ
  secondOrderCoeff_nonneg : 0 ≤ secondOrderCoeff
  error_bound : p09ComplexRms (p09FftRoundoffError run) ≤
    model.epsilon * Real.sqrt (n : ℝ) * p09K plan model.gamma *
        p09ComplexRms run.input +
      secondOrderCoeff * model.epsilon ^ 2

end HighamBench
