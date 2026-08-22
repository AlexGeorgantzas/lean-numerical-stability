import HighamBench.Core
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

/-- The explicit finite maximum of the absolute vector coefficients used as
the infinity norm around equations (3.1)--(3.4). -/
noncomputable def p20InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => Real.toNNReal |x i|) : NNReal) : ℝ)

/-- Scale a finite row or column by a real power-of-two factor. -/
def p20ScaleVec {n : ℕ} (lambda : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda * x i

/-- The largest safe scaled-input magnitude from equation (3.2). -/
noncomputable def p20ScalingThreshold (n : ℕ) (fmax Fmax : ℝ) : ℝ :=
  min fmax (Real.sqrt (Fmax / (n : ℝ)))

/-- Exact powers of two used for the diagonal scaling factors in (3.1). -/
def p20IsPowerOfTwo (lambda : ℝ) : Prop :=
  ∃ exponent : ℤ, lambda = (2 : ℝ) ^ exponent

/-- Select the exponent whose power of two lies immediately below
`theta / ‖x‖∞`. The fallback is irrelevant for the positive ratios required
by equation (3.4a). -/
noncomputable def p20RowScaleExponent {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℤ :=
  if hratio : 0 < theta / p20InfNormVec x then
    Classical.choose
      (exists_mem_Ico_zpow hratio (by norm_num : (1 : ℝ) < 2))
  else
    0

/-- The row-specific power-of-two factor `lambda_i` selected for (3.4a). -/
noncomputable def p20RowScaleFactor {n : ℕ}
    (theta : ℝ) (x : Fin n → ℝ) : ℝ :=
  (2 : ℝ) ^ p20RowScaleExponent theta x

/-- The diagonal matrix `Lambda` from equation (3.1). -/
noncomputable def p20RowScalingMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal (fun i => p20RowScaleFactor theta (A i))

/-- The exactly scaled input `Lambda A` from equation (3.1). -/
noncomputable def p20LeftScaledMatrix {m n : ℕ}
    (theta : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  p20RowScalingMatrix theta A * A

/-- Paper-scoped rectangular infinity norm (maximum absolute row sum). -/
noncomputable def p20InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

/-- The input-underflow part of the simplified single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowBound {m n q : ℕ}
    (theta gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The accumulation-underflow part of the simplified single-word bound
(3.26). -/
noncomputable def p20SingleAccumUnderflowBound {m n q : ℕ}
    (theta Gmin : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  (4 * (n : ℝ) ^ 2 * (theta⁻¹) ^ 2 * Gmin) *
    p20InfNormRect A * p20InfNormRect B

/-- The input-rounding term in the multiword bound (4.32). -/
def p20MultiInputRoundingCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p

/-- The input-rounding term in the single-word bound (3.26). -/
def p20SingleInputRoundingCoefficient (u : ℝ) : ℝ :=
  2 * u

/-- The input-underflow coefficient in the single-word bound (3.26). -/
noncomputable def p20SingleInputUnderflowCoefficient
    (n : ℕ) (theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin

/-- The accumulation-rounding term in the multiword bound (4.32). -/
def p20MultiAccumRoundingCoefficient (n p : ℕ) (U : ℝ) : ℝ :=
  ((n : ℝ) + (p : ℝ) ^ 2) * U

/-- The range-unrestricted coefficient in the multiword bound (4.33). -/
def p20MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  p20MultiInputRoundingCoefficient p u +
    p20MultiAccumRoundingCoefficient n p U

/-- The input-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

/-- The accumulation-underflow term added in the multiword bound (4.32). -/
noncomputable def p20MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

/-- The complete narrow-range coefficient in the multiword bound (4.32). -/
noncomputable def p20MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p20MultiRangeFreeCoefficient n p u U +
    p20MultiInputUnderflowCoefficient n p u theta gmin +
      p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- Apply a scalar coefficient to the product of the two rectangular matrix
infinity norms appearing in (3.26), (4.32), and (4.33). -/
noncomputable def p20NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p20InfNormRect A * p20InfNormRect B

/-! ## Multiword execution model for Theorem 4.1 -/

/-- A finite rectangular real matrix in the P20 model. -/
abbrev P20Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The unit roundoff `2^(-t)` of a binary format with `t` precision bits. -/
noncomputable def p20UnitRoundoff (precision : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ precision

/-- The smallest positive normalized value of a binary format. -/
noncomputable def p20MinNormal (minExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ minExponent

/-- The largest finite value of the binary format used in Model 1. -/
noncomputable def p20MaxFinite (precision : ℕ) (maxExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ maxExponent * (2 - 2 * p20UnitRoundoff precision)

/-- The `g_min` or `G_min` envelope from (2.1)--(2.2). -/
noncomputable def p20UnderflowEnvelope (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) : ℝ :=
  match hasSubnormals with
  | false => p20MinNormal minExponent / 2
  | true => p20UnitRoundoff precision * p20MinNormal minExponent

/-- A precision-parametrized binary floating-point format from Model 1. -/
structure P20BinaryFormatFamily (ι : Type*) where
  precision : ι → ℕ
  minExponent : ι → ℤ
  maxExponent : ι → ℤ
  hasSubnormals : ι → Bool
  precision_pos : ∀ t, 0 < precision t
  exponent_range_nonempty : ∀ t, minExponent t ≤ maxExponent t

/-- Unit roundoff of one member of a format family. -/
noncomputable def p20FormatUnitRoundoff {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnitRoundoff (format.precision t)

/-- Largest finite value of one member of a format family. -/
noncomputable def p20FormatMaxFinite {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20MaxFinite (format.precision t) (format.maxExponent t)

/-- Underflow envelope of one member of a format family. -/
noncomputable def p20FormatUnderflowEnvelope {ι : Type*}
    (format : P20BinaryFormatFamily ι) (t : ι) : ℝ :=
  p20UnderflowEnvelope (format.precision t) (format.minExponent t)
    (format.hasSubnormals t)

/-- Model 1: input and accumulation formats, their nesting, and the two
rounding models (2.3)--(2.4). The maps represent operations for which overflow
does not occur. -/
structure P20Model1 (ι : Type*) where
  inputFormat : P20BinaryFormatFamily ι
  accumulationFormat : P20BinaryFormatFamily ι
  accumulation_precision : ∀ t,
    inputFormat.precision t ≤ accumulationFormat.precision t
  accumulation_range : ∀ t,
    accumulationFormat.minExponent t ≤ inputFormat.minExponent t ∧
      inputFormat.maxExponent t ≤ accumulationFormat.maxExponent t
  inputRound : ι → ℝ → ℝ
  inputDelta : ι → ℝ → ℝ
  inputEta : ι → ℝ → ℝ
  input_rounding_equation : ∀ t x,
    inputRound t x = x * (1 + inputDelta t x) + inputEta t x
  input_delta_bound : ∀ t x,
    |inputDelta t x| ≤ p20FormatUnitRoundoff inputFormat t
  input_eta_bound : ∀ t x,
    |inputEta t x| ≤ p20FormatUnderflowEnvelope inputFormat t
  input_error_exclusive : ∀ t x, inputEta t x * inputDelta t x = 0
  accumulationRound : ι → ℝ → ℝ
  accumulationDelta : ι → ℝ → ℝ
  accumulationEta : ι → ℝ → ℝ
  accumulation_rounding_equation : ∀ t x,
    accumulationRound t x =
      x * (1 + accumulationDelta t x) + accumulationEta t x
  accumulation_delta_bound : ∀ t x,
    |accumulationDelta t x| ≤
      p20FormatUnitRoundoff accumulationFormat t
  accumulation_eta_bound : ∀ t x,
    |accumulationEta t x| ≤
      p20FormatUnderflowEnvelope accumulationFormat t
  accumulation_error_exclusive : ∀ t x,
    accumulationEta t x * accumulationDelta t x = 0

/-- The input-format unit roundoff `u` of Model 1. -/
noncomputable def p20InputUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.inputFormat t

/-- The accumulation-format unit roundoff `U` of Model 1. -/
noncomputable def p20AccumUnitRoundoff {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnitRoundoff model.accumulationFormat t

/-- The input-format underflow envelope `g_min` of Model 1. -/
noncomputable def p20InputUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.inputFormat t

/-- The accumulation-format underflow envelope `G_min` of Model 1. -/
noncomputable def p20AccumUnderflowEnvelope {ι : Type*}
    (model : P20Model1 ι) (t : ι) : ℝ :=
  p20FormatUnderflowEnvelope model.accumulationFormat t

/-- The format-derived scaling threshold `theta` from (3.2). -/
noncomputable def p20ModelScalingThreshold {ι : Type*}
    (n : ℕ) (model : P20Model1 ι) (t : ι) : ℝ :=
  p20ScalingThreshold n
    (p20FormatMaxFinite model.inputFormat t)
    (p20FormatMaxFinite model.accumulationFormat t)

/-- Exact row scaling by the diagonal entries of `Lambda`. -/
def p20ScaleRows {m n : ℕ} (lambda : Fin m → ℝ)
    (A : P20Matrix m n) : P20Matrix m n :=
  fun i j => lambda i * A i j

/-- Exact column scaling by the diagonal entries of `M`. -/
def p20ScaleColumns {n q : ℕ} (B : P20Matrix n q)
    (mu : Fin q → ℝ) : P20Matrix n q :=
  fun i j => B i j * mu j

/-- The maximal-power-of-two scaling rule inherited from (3.4a)--(3.4b).
The zero-vector branch records an explicit harmless convention omitted by the
paper. -/
def p20MaximalPowerTwoScale (theta vectorNorm lambda : ℝ) : Prop :=
  p20IsPowerOfTwo lambda ∧ 0 < lambda ∧
    ((vectorNorm = 0 ∧ lambda = 1) ∨
      (0 < vectorNorm ∧ theta / (2 * vectorNorm) < lambda ∧
        lambda ≤ theta / vectorNorm))

/-! ## Single-word scaled-input error from equations (3.3)--(3.13) -/

/-- The exact absolute inner product `|x|^T |y|` in (3.9)--(3.14). -/
noncomputable def p20AbsInnerProduct {n : ℕ}
    (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| * |y i|

/-- The scaled and componentwise input-rounded inner product `s` from (3.3),
before any accumulation-format rounding is applied. -/
noncomputable def p20ScaledInputInnerProduct {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (lambda mu : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  lambda⁻¹ * mu⁻¹ *
    ∑ i : Fin n,
      model.inputRound t (lambda * x i) *
        model.inputRound t (mu * y i)

/-- The input-rounding and input-underflow error `epsilon_1` from (3.8). -/
noncomputable def p20InputStageError {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (lambda mu : ℝ)
    (x y : Fin n → ℝ) : ℝ :=
  p20ScaledInputInnerProduct model t lambda mu x y -
    ∑ i : Fin n, x i * y i

/-- The exact right-hand side of equation (3.13). -/
noncomputable def p20InputStageErrorEnvelope {n : ℕ}
    (u gmin theta : ℝ) (x y : Fin n → ℝ) : ℝ :=
  (2 * u + u ^ 2) * p20AbsInnerProduct x y +
    4 * (n : ℝ) * theta⁻¹ * gmin *
      (1 + u + theta⁻¹ * gmin) *
        p20InfNormVec x * p20InfNormVec y

/-- An accumulation-format inner product. Each multiply-add result is rounded
by the accumulation map from Model 1. -/
noncomputable def p20AccumulatedInnerProduct {n : ℕ}
    (round : ℝ → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (List.ofFn fun k : Fin n => x k * y k).foldl
    (fun sum product => round (sum + product)) 0

/-- The retained word-index pairs from (4.31), in lexicographic execution
order. -/
def p20RetainedWordPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.ofFn fun i : Fin p =>
    (List.ofFn fun j : Fin p => (i, j)).filter
      (fun pair => decide (pair.1.val + pair.2.val < p))).flatten

/-- The accumulated expression inside the inverse scalings in (4.31): retain
precisely the word pairs with `i+j<p`, weight them by `u^(i+j)`, and round
their running sum in the accumulation format. -/
noncomputable def p20RetainedWordProduct {m n q p : ℕ}
    (round : ℝ → ℝ) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    (p20RetainedWordPairs p).foldl
      (fun sum pair =>
        round
          (sum + u ^ (pair.1.val + pair.2.val) *
            p20AccumulatedInnerProduct round (Aword pair.1 row)
              (fun k => Bword pair.2 k col))) 0

/-- Undo the diagonal row and column scalings around the retained word
product, as in (4.31). -/
noncomputable def p20UnscaleProduct {m q : ℕ} (lambda : Fin m → ℝ)
    (mu : Fin q → ℝ) (C : P20Matrix m q) : P20Matrix m q :=
  fun i j => (lambda i)⁻¹ * C i j * (mu j)⁻¹

/-- One computed instance of the scaled p-word algorithm (4.29)--(4.31).
The scaling clauses include the lower endpoints used in the derivation of
Theorem 4.1, not only the upper bounds printed in its statement. -/
structure P20MultiwordRun (m n q p : ℕ) (ι : Type*) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20Model1 ι
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : ι → Fin m → ℝ
  columnScale : ι → Fin q → ℝ
  row_scaling_rule : ∀ t i,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (A i)) (rowScale t i)
  column_scaling_rule : ∀ t j,
    p20MaximalPowerTwoScale (p20ModelScalingThreshold n model t)
      (p20InfNormVec (fun i => B i j)) (columnScale t j)
  scaled_A_bound : ∀ t i j,
    |p20ScaleRows (rowScale t) A i j| ≤
      p20ModelScalingThreshold n model t
  scaled_B_bound : ∀ t i j,
    |p20ScaleColumns B (columnScale t) i j| ≤
      p20ModelScalingThreshold n model t
  Aword : ι → Fin p → P20Matrix m n
  Bword : ι → Fin p → P20Matrix n q
  Aword_equation : ∀ t i row col,
    Aword t i row col = model.inputRound t
      ((p20ScaleRows (rowScale t) A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Aword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  Bword_equation : ∀ t i row col,
    Bword t i row col = model.inputRound t
      ((p20ScaleColumns B (columnScale t) row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k =>
              p20InputUnitRoundoff model t ^ k.val * Bword t k row col)) /
        p20InputUnitRoundoff model t ^ i.val)
  computed : ι → P20Matrix m q
  computed_equation : ∀ t,
    computed t = p20UnscaleProduct (rowScale t) (columnScale t)
      (p20RetainedWordProduct (model.accumulationRound t)
        (p20InputUnitRoundoff model t) (Aword t) (Bword t))

/-- Reconstruct `A` from all `p` input words and undo `Lambda`, as in (4.18). -/
noncomputable def p20AWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m n :=
  fun row col =>
    (run.rowScale t row)⁻¹ *
      ∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Aword t i row col

/-- Reconstruct `B` from all `p` input words and undo `M`, as in (4.19). -/
noncomputable def p20BWordApproximation {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20InputUnitRoundoff run.model t ^ i.val * run.Bword t i row col) *
      (run.columnScale t col)⁻¹

/-- The retained part of (4.31) with exact inner products and exact summation.
Its difference from the computed value isolates accumulation-format errors. -/
noncomputable def p20ExactRetainedWordProduct {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The products omitted from (4.31), namely all word pairs with `i+j>=p`. -/
noncomputable def p20OmittedWordTail {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : P20Matrix m q :=
  p20UnscaleProduct (run.rowScale t) (run.columnScale t)
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20InputUnitRoundoff run.model t ^ (i.val + j.val) *
              (run.Aword t i * run.Bword t j) row col))

/-- The actual normwise forward error of one execution of (4.31). -/
noncomputable def p20MultiwordForwardError {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (t : ι) : ℝ :=
  p20InfNormRect (run.computed t - run.A * run.B)

/-- The combined first-order scale whose square classifies the terms hidden
by `lesssim` in (4.26)--(4.32). Dimensions and `p` are fixed along the filter. -/
noncomputable def p20MultiwordPrecisionScale {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) : ι → ℝ :=
  fun t =>
    p20InputUnitRoundoff run.model t ^ p +
      p20InputUnitRoundoff run.model t ^ (p - 1) *
        (p20ModelScalingThreshold n run.model t)⁻¹ *
          p20InputUnderflowEnvelope run.model t +
      p20AccumUnitRoundoff run.model t +
      (p20ModelScalingThreshold n run.model t)⁻¹ ^ 2 *
        p20AccumUnderflowEnvelope run.model t

/-- A scalar or norm remainder that is second order in the precision scale. -/
def p20SecondOrderAt {ι : Type*} (l : Filter ι)
    (scale remainder : ι → ℝ) : Prop :=
  remainder =O[l] fun t => scale t ^ 2

/-- A precise first-order interpretation of the paper's `lesssim`: the
displayed inequality holds modulo an explicitly second-order remainder. -/
def p20FirstOrderLeAt {ι : Type*} (l : Filter ι)
    (scale lhs rhs : ι → ℝ) : Prop :=
  ∃ remainder : ι → ℝ,
    p20SecondOrderAt l scale remainder ∧
      ∀ᶠ t in l, lhs t ≤ rhs t + |remainder t|

/-- The exact decomposition identities from (4.18)--(4.24), split into
relative-rounding and underflow parts. These identities tie every subsequent
contribution to the words and computed matrix in `run`. -/
structure P20MultiwordErrorData {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) where
  AInputRoundingError : ι → P20Matrix m n
  AInputUnderflowError : ι → P20Matrix m n
  BInputRoundingError : ι → P20Matrix n q
  BInputUnderflowError : ι → P20Matrix n q
  accumulationRoundingError : ι → P20Matrix m q
  accumulationUnderflowError : ι → P20Matrix m q
  A_decomposition : ∀ t,
    run.A = p20AWordApproximation run t + AInputRoundingError t +
      AInputUnderflowError t
  B_decomposition : ∀ t,
    run.B = p20BWordApproximation run t + BInputRoundingError t +
      BInputUnderflowError t
  retained_partition : ∀ t,
    p20ExactRetainedWordProduct run t =
      p20AWordApproximation run t * p20BWordApproximation run t -
        p20OmittedWordTail run t
  accumulation_decomposition : ∀ t,
    run.computed t = p20ExactRetainedWordProduct run t +
      accumulationRoundingError t + accumulationUnderflowError t
  A_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    AInputRoundingError t = 0
  B_rounding_zero : ∀ t, run.model.inputDelta t = 0 →
    BInputRoundingError t = 0
  A_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    AInputUnderflowError t = 0
  B_underflow_zero : ∀ t, run.model.inputEta t = 0 →
    BInputUnderflowError t = 0
  accumulation_rounding_zero : ∀ t, run.model.accumulationDelta t = 0 →
    accumulationRoundingError t = 0
  accumulation_underflow_zero : ∀ t, run.model.accumulationEta t = 0 →
    accumulationUnderflowError t = 0

/-- The first-order input-rounding contribution: the two linear decomposition
errors and the omitted `i+j>=p` tail. -/
noncomputable def p20InputRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputRoundingError t * run.B) -
    run.A * data.BInputRoundingError t - p20OmittedWordTail run t

/-- The two linear input-underflow contributions. -/
noncomputable def p20InputUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  -(data.AInputUnderflowError t * run.B) -
    run.A * data.BInputUnderflowError t

/-- The accumulation-rounding contribution in the exact computed output. -/
def p20AccumRoundingContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationRoundingError t

/-- The accumulation-underflow contribution in the exact computed output. -/
def p20AccumUnderflowContribution {m n q p : ℕ} {ι : Type*}
    {run : P20MultiwordRun m n q p ι}
    (data : P20MultiwordErrorData run) (t : ι) : P20Matrix m q :=
  data.accumulationUnderflowError t

/-- The exact residual after removing the four displayed first-order
contributions from the actual computed forward-error matrix. -/
noncomputable def p20ForwardRemainder {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) : P20Matrix m q :=
  run.computed t - run.A * run.B - p20InputRoundingContribution data t -
    p20InputUnderflowContribution data t -
      p20AccumRoundingContribution data t -
        p20AccumUnderflowContribution data t

/-- Exact additive decomposition of the computed forward error. -/
theorem p20ForwardError_decomposition {m n q p : ℕ} {ι : Type*}
    (run : P20MultiwordRun m n q p ι) (data : P20MultiwordErrorData run)
    (t : ι) :
    run.computed t - run.A * run.B =
      p20InputRoundingContribution data t +
        p20InputUnderflowContribution data t +
          p20AccumRoundingContribution data t +
            p20AccumUnderflowContribution data t +
              p20ForwardRemainder run data t := by
  unfold p20ForwardRemainder
  abel

/-- The four-source propagation certificate for the derivation
(4.18)--(4.28). It stores source-derived component estimates and a second-order
remainder, but not the final bound (4.32). -/
structure P20MultiwordForwardAnalysis {m n q p : ℕ} {ι : Type*}
    {l : Filter ι} (run : P20MultiwordRun m n q p ι) where
  data : P20MultiwordErrorData run
  input_rounding_bound : ∀ t,
    p20InfNormRect (p20InputRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputRoundingCoefficient p
          (p20InputUnitRoundoff run.model t)) run.A run.B
  input_underflow_bound : ∀ t,
    p20InfNormRect (p20InputUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiInputUnderflowCoefficient n p
          (p20InputUnitRoundoff run.model t)
          (p20ModelScalingThreshold n run.model t)
          (p20InputUnderflowEnvelope run.model t)) run.A run.B
  accumulation_rounding_bound : ∀ t,
    p20InfNormRect (p20AccumRoundingContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumRoundingCoefficient n p
          (p20AccumUnitRoundoff run.model t)) run.A run.B
  accumulation_underflow_bound : ∀ t,
    p20InfNormRect (p20AccumUnderflowContribution data t) ≤
      p20NormwiseEnvelope
        (p20MultiAccumUnderflowCoefficient n p
          (p20ModelScalingThreshold n run.model t)
          (p20AccumUnderflowEnvelope run.model t)) run.A run.B
  remainder_second_order :
    p20SecondOrderAt l (p20MultiwordPrecisionScale run)
      (fun t => p20InfNormRect (p20ForwardRemainder run data t))

/-- Dot-notation projection of the fixed higher-order remainder. -/
noncomputable def P20MultiwordForwardAnalysis.remainder
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20ForwardRemainder run analysis.data

/-- Dot-notation projection of the fixed input-rounding contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputRoundingContribution analysis.data

/-- Dot-notation projection of the fixed input-underflow contribution. -/
noncomputable def P20MultiwordForwardAnalysis.inputUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20InputUnderflowContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-rounding contribution. -/
def P20MultiwordForwardAnalysis.accumulationRoundingContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumRoundingContribution analysis.data

/-- Dot-notation projection of the fixed accumulation-underflow contribution. -/
def P20MultiwordForwardAnalysis.accumulationUnderflowContribution
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) :
    ι → P20Matrix m q :=
  p20AccumUnderflowContribution analysis.data

/-- Dot-notation form of the exact additive decomposition. -/
theorem P20MultiwordForwardAnalysis.error_decomposition
    {m n q p : ℕ} {ι : Type*} {l : Filter ι}
    {run : P20MultiwordRun m n q p ι}
    (analysis : P20MultiwordForwardAnalysis (l := l) run) (t : ι) :
    run.computed t - run.A * run.B =
      analysis.inputRoundingContribution t +
        analysis.inputUnderflowContribution t +
          analysis.accumulationRoundingContribution t +
            analysis.accumulationUnderflowContribution t +
              analysis.remainder t := by
  exact p20ForwardError_decomposition run analysis.data t

/-- A proof-carrying execution of every hypothesis and intermediate error
category used to obtain Theorem 4.1. -/
structure P20Theorem41Execution (m n q p : ℕ) (ι : Type*)
    (l : Filter ι) where
  run : P20MultiwordRun m n q p ι
  analysis : P20MultiwordForwardAnalysis (l := l) run

/-! ## Static Theorem 4.1 reconstruction -/

/-- A fixed-instance interpretation of the paper's first-order comparison.
The predicate classifying omitted terms is closed under the operations needed
to combine the independently derived Section 4 remainders. -/
structure P20FirstOrderSemantics where
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0
  add_secondOrder : ∀ {x y}, secondOrder x → secondOrder y →
    secondOrder (x + y)
  abs_secondOrder : ∀ {x}, secondOrder x → secondOrder |x|

/-- The fixed, pointwise meaning of `lhs lesssim rhs`: an exact inequality
after retaining one scalar term classified as second order. -/
def p20FirstOrderLe (semantics : P20FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

/-- The integer parameters of one fixed binary format. -/
structure P20StaticBinaryFormat where
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  hasSubnormals : Bool
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent ≤ maxExponent

/-- The finite real values represented by a fixed binary format. Normal
significands have `precision` bits. When enabled, subnormals use the same
spacing at `minExponent` and a shorter positive significand. -/
def p20StaticRepresentable (format : P20StaticBinaryFormat)
    (x : ℝ) : Prop :=
  x = 0 ∨
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ significand : ℕ, ∃ exponent : ℤ,
        x = sign * (significand : ℝ) *
            (2 : ℝ) ^
              (exponent - (format.precision - 1 : ℕ)) ∧
          ((2 ^ (format.precision - 1) ≤ significand ∧
              significand < 2 ^ format.precision ∧
              format.minExponent ≤ exponent ∧
              exponent ≤ format.maxExponent) ∨
            (format.hasSubnormals = true ∧
              exponent = format.minExponent ∧
              0 < significand ∧
              significand < 2 ^ (format.precision - 1)))

/-- Model 1 at one fixed pair of formats. The inherited error equations are
supplemented with the source's default round-to-nearest meaning. The
`NoOverflow` predicates delimit the operations on which rounding is defined;
the algorithm below certifies that every operation it executes lies there. -/
structure P20StaticNearestModel1 where
  inputFormat : P20StaticBinaryFormat
  accumulationFormat : P20StaticBinaryFormat
  accumulation_precision :
    inputFormat.precision ≤ accumulationFormat.precision
  accumulation_range :
    accumulationFormat.minExponent ≤ inputFormat.minExponent ∧
      inputFormat.maxExponent ≤ accumulationFormat.maxExponent
  inputRound : ℝ → ℝ
  inputDelta : ℝ → ℝ
  inputEta : ℝ → ℝ
  inputNoOverflow : ℝ → Prop
  input_rounding_equation : ∀ {x}, inputNoOverflow x →
    inputRound x = x * (1 + inputDelta x) + inputEta x
  input_delta_bound : ∀ {x}, inputNoOverflow x →
    |inputDelta x| ≤ p20UnitRoundoff inputFormat.precision
  input_eta_bound : ∀ {x}, inputNoOverflow x →
    |inputEta x| ≤
      p20UnderflowEnvelope inputFormat.precision inputFormat.minExponent
        inputFormat.hasSubnormals
  input_error_exclusive : ∀ {x}, inputNoOverflow x →
    inputEta x * inputDelta x = 0
  input_round_representable : ∀ {x}, inputNoOverflow x →
    p20StaticRepresentable inputFormat (inputRound x)
  input_round_nearest : ∀ {x}, inputNoOverflow x →
    ∀ {y}, p20StaticRepresentable inputFormat y →
      |inputRound x - x| ≤ |y - x|
  accumulationRound : ℝ → ℝ
  accumulationDelta : ℝ → ℝ
  accumulationEta : ℝ → ℝ
  accumulationNoOverflow : ℝ → Prop
  accumulation_rounding_equation : ∀ {x}, accumulationNoOverflow x →
    accumulationRound x =
      x * (1 + accumulationDelta x) + accumulationEta x
  accumulation_delta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationDelta x| ≤
      p20UnitRoundoff accumulationFormat.precision
  accumulation_eta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationEta x| ≤
      p20UnderflowEnvelope accumulationFormat.precision
        accumulationFormat.minExponent accumulationFormat.hasSubnormals
  accumulation_error_exclusive : ∀ {x}, accumulationNoOverflow x →
    accumulationEta x * accumulationDelta x = 0
  accumulation_round_representable : ∀ {x}, accumulationNoOverflow x →
    p20StaticRepresentable accumulationFormat (accumulationRound x)
  accumulation_round_nearest : ∀ {x}, accumulationNoOverflow x →
    ∀ {y}, p20StaticRepresentable accumulationFormat y →
      |accumulationRound x - x| ≤ |y - x|

/-- Input-format unit roundoff in the fixed Model-1 contract. -/
noncomputable def p20StaticInputUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.inputFormat.precision

/-- Accumulation-format unit roundoff in the fixed Model-1 contract. -/
noncomputable def p20StaticAccumUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.accumulationFormat.precision

/-- Input-format underflow envelope in the fixed Model-1 contract. -/
noncomputable def p20StaticInputUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.inputFormat.precision
    model.inputFormat.minExponent model.inputFormat.hasSubnormals

/-- Accumulation-format underflow envelope in the fixed Model-1 contract. -/
noncomputable def p20StaticAccumUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.accumulationFormat.precision
    model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals

/-- The fixed threshold `theta = min(fmax, sqrt(Fmax / n))`. -/
noncomputable def p20StaticScalingThreshold (n : ℕ)
    (model : P20StaticNearestModel1) : ℝ :=
  p20ScalingThreshold n
    (p20MaxFinite model.inputFormat.precision
      model.inputFormat.maxExponent)
    (p20MaxFinite model.accumulationFormat.precision
      model.accumulationFormat.maxExponent)

/-- A rounded left fold, used only after every exact product has itself been
rounded to the accumulation format. -/
def p20RoundedFoldFrom (round : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | acc, [] => acc
  | acc, term :: terms =>
      p20RoundedFoldFrom round (round (acc + term)) terms

/-- Every addition argument visited by `p20RoundedFoldFrom` is in the
no-overflow domain. -/
def p20RoundedFoldNoOverflowFrom (allowed : ℝ → Prop)
    (round : ℝ → ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, term :: terms =>
      allowed (acc + term) ∧
        p20RoundedFoldNoOverflowFrom allowed round
          (round (acc + term)) terms

/-- An accumulation-format inner product that rounds each multiplication and
then each addition, as required by equation (2.4). -/
noncomputable def p20StaticAccumulatedInnerProduct {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : ℝ :=
  p20RoundedFoldFrom model.accumulationRound 0
    ((List.ofFn fun k : Fin n =>
      model.accumulationRound (x k * y k)))

/-- No overflow occurs in either the multiplications or the additions of one
executed accumulation-format inner product. -/
def p20StaticInnerProductNoOverflow {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : Prop :=
  (∀ k, model.accumulationNoOverflow (x k * y k)) ∧
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        (List.ofFn fun k : Fin n =>
          model.accumulationRound (x k * y k))

/-- The triangular computation in (4.31). Each retained matrix-product inner
product is executed by `p20StaticAccumulatedInnerProduct`, and the retained
word products are then added in the accumulation format. The powers of `u`
are exact binary scalings. -/
noncomputable def p20StaticRetainedWordProduct {m n q p : ℕ}
    (model : P20StaticNearestModel1) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    p20RoundedFoldFrom model.accumulationRound 0
      ((p20RetainedWordPairs p).map (fun pair =>
        u ^ (pair.1.val + pair.2.val) *
          p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
            (fun k => Bword pair.2 k col)))

/-- One fixed execution of equations (4.29)-(4.31). It contains no propagated
error estimate or final theorem bound. -/
structure P20StaticMultiwordRun (m n q p : ℕ) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20StaticNearestModel1
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : Fin m → ℝ
  columnScale : Fin q → ℝ
  row_scaling_rule : ∀ i,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (A i)) (rowScale i)
  column_scaling_rule : ∀ j,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (fun i => B i j)) (columnScale j)
  scaled_A_bound : ∀ i j,
    |p20ScaleRows rowScale A i j| ≤ p20StaticScalingThreshold n model
  scaled_B_bound : ∀ i j,
    |p20ScaleColumns B columnScale i j| ≤
      p20StaticScalingThreshold n model
  Aword : Fin p → P20Matrix m n
  Bword : Fin p → P20Matrix n q
  Aword_equation : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    Aword i row col = model.inputRound
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Aword_no_overflow : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    model.inputNoOverflow
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_equation : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    Bword i row col = model.inputRound
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_no_overflow : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    model.inputNoOverflow
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  accumulation_no_overflow : ∀ (i j : Fin p),
    i.val + j.val < p → ∀ (row : Fin m) (col : Fin q),
      p20StaticInnerProductNoOverflow model (Aword i row)
        (fun k => Bword j k col)
  retained_sum_no_overflow : ∀ (row : Fin m) (col : Fin q),
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        ((p20RetainedWordPairs p).map (fun pair =>
          p20StaticInputUnitRoundoff model ^
              (pair.1.val + pair.2.val) *
            p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
              (fun k => Bword pair.2 k col)))
  computed : P20Matrix m q
  computed_equation :
    computed = p20UnscaleProduct rowScale columnScale
      (p20StaticRetainedWordProduct model
        (p20StaticInputUnitRoundoff model) Aword Bword)

/-- Reconstruct `A` from all p words and undo the row scaling. -/
noncomputable def p20StaticAWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m n :=
  fun row col =>
    (run.rowScale row)⁻¹ *
      ∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Aword i row col

/-- Reconstruct `B` from all p words and undo the column scaling. -/
noncomputable def p20StaticBWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Bword i row col) *
      (run.columnScale col)⁻¹

/-- The retained p-word product with exact real inner products. -/
noncomputable def p20StaticExactRetainedWordProduct {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

/-- The word products omitted by the triangular condition `i+j<p`. -/
noncomputable def p20StaticOmittedWordTail {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

/-- The accumulation-format error of the actually executed retained product. -/
noncomputable def p20StaticAccumulationError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  run.computed - p20StaticExactRetainedWordProduct run

/-- The fixed normwise forward error in Theorem 4.1. -/
noncomputable def p20StaticMultiwordForwardError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  p20InfNormRect (run.computed - run.A * run.B)

/-- The decomposition coefficient zeta from equation (4.20). -/
noncomputable def p20StaticZeta {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  max (p20StaticInputUnitRoundoff run.model ^ p)
    (2 * (n : ℝ) * p20StaticInputUnitRoundoff run.model ^ (p - 1) *
      (p20StaticScalingThreshold n run.model)⁻¹ *
        p20StaticInputUnderflowEnvelope run.model)

/-- The omitted-product coefficient in equation (4.26). -/
def p20StaticOmittedCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) - 1) * u ^ p

/-- The final accumulation coefficient after applying the source's bound on
the number `r` of possible underflows in one output coefficient. -/
noncomputable def p20StaticAccumulationCoefficient
    (n p : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    p20MultiAccumUnderflowCoefficient n p theta Gmin

/-- The unsimplified coefficient in (4.27), before substituting the bound on
the possible-underflow count `r`. -/
noncomputable def p20StaticRawAccumulationCoefficient
    (n p r : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    4 * (r : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin

/-- The source-local Section 4 estimates used before Theorem 4.1. This stores
the matrix and retained-product decompositions needed to derive (4.21)-(4.25),
the two zeta bounds, and the separate pre-theorem estimates (4.26)-(4.27). It
does not contain (4.28), (4.32), the collected four-term coefficient, or a
final forward-error bound. -/
structure P20StaticSection4Derivation
    (semantics : P20FirstOrderSemantics) {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) where
  AError : P20Matrix m n
  BError : P20Matrix n q
  A_decomposition :
    run.A = p20StaticAWordApproximation run + AError
  B_decomposition :
    run.B = p20StaticBWordApproximation run + BError
  A_error_bound :
    p20InfNormRect AError ≤ p20StaticZeta run * p20InfNormRect run.A
  B_error_bound :
    p20InfNormRect BError ≤ p20StaticZeta run * p20InfNormRect run.B
  retained_partition :
    p20StaticExactRetainedWordProduct run =
      p20StaticAWordApproximation run *
          p20StaticBWordApproximation run -
        p20StaticOmittedWordTail run
  omittedRemainder : ℝ
  omitted_remainder_second_order :
    semantics.secondOrder omittedRemainder
  omitted_tail_bound :
    p20InfNormRect (p20StaticOmittedWordTail run) ≤
      p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        |omittedRemainder|
  accumulationRemainder : ℝ
  accumulation_remainder_second_order :
    semantics.secondOrder accumulationRemainder
  underflowCount : ℕ
  underflow_count_bound :
    (underflowCount : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2
  accumulation_error_bound :
    p20InfNormRect (p20StaticAccumulationError run) ≤
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        |accumulationRemainder|
  quadratic_second_order :
    semantics.secondOrder
      (p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B)

end HighamBench
