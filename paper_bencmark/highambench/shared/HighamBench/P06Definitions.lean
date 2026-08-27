import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace HighamBench

open scoped BigOperators

/-- Euclidean norm in the finite real-vector notation used by P06. -/
noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular Frobenius norm in P06's finite matrix notation. -/
noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Identity matrix on an arbitrary finite decidable index type. -/
noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Matrix multiplication for an `m`-by-`m` matrix acting on an
`m`-by-`n` matrix. -/
noncomputable def p06RectMatMul {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin m, Q i k * R k j

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The homogeneous rectangular operator-2 upper-bound predicate. -/
def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

/-- The Householder matrix `I - vvᵀ` in the normalization `vᵀv = 2`
used in section 4 of P06. -/
noncomputable def p06HouseholderMatrix {m : ℕ}
    (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ p06FiniteId i j - v i * v j

/-- Exact orthogonality, written as `QᵀQ = I`. -/
def p06Orthogonal {m : ℕ} (Q : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, (∑ k : Fin m, Q k i * Q k j) = p06FiniteId i j

/-- An `m`-by-`n` matrix is upper trapezoidal when all entries strictly
below its main diagonal are zero. -/
def p06UpperTrapezoidal {m n : ℕ}
    (R : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

/-- The probabilistic accumulated-error constant in P06 equation (1.6). -/
noncomputable def p06GammaTilde (k : ℕ) (lambda u : ℝ) : ℝ :=
  Real.exp
      ((lambda * Real.sqrt (k : ℝ) * u + (k : ℝ) * u ^ 2) /
        (1 - u)) -
    1

/-- The leading coefficient in Theorem 4.4 and equation (4.20). -/
noncomputable def p06QRLeadingCoefficient
    (c6 : ℕ) (lambda : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  (c6 : ℝ) * lambda * Real.sqrt (n : ℝ) *
    p06GammaTilde m lambda u

/-- The probability lower bound `p₄(lambda,m,n)` attached to the simultaneous
columnwise event in Theorem 4.4. It is intentionally allowed to be negative
for small `lambda`, exactly as in the paper. -/
noncomputable def p06P4 (lambda : ℝ) (m n : ℕ) : ℝ :=
  1 - 2 * (m : ℝ) * (n : ℝ) * Real.exp (-lambda ^ 2)

/-- A scalar remainder of order `u²` as unit roundoff tends to zero. The
definition deliberately does not choose an input-norm scale or uniformity in
the dimensions, neither of which is specified by equation (4.20). -/
def p06SecondOrderAtZero (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhds 0] fun u : ℝ ↦ u ^ 2

/-- The one-sided `O(u²)` interpretation used when unit roundoff ranges over
strictly positive values below one. -/
def p06SecondOrderAtZeroRight (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] fun u : ℝ ↦ u ^ 2

/-- A second-order remainder whose asymptotic witness also controls every
unit roundoff between zero and the distinguished execution's unit roundoff.
This closes the gap between a limit statement at zero and evaluation at one
fixed positive value of `u`. -/
def P06SecondOrderControl (remainder : ℝ → ℝ) (u0 : ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧
    p06SecondOrderAtZero remainder ∧
    ∀ u, |u| ≤ |u0| → |remainder u| ≤ constant * u ^ 2

/-- Errors generated before operation `k`, in the computation order used by
Model 1.5. -/
def p06PriorErrors {Ω : Type*} {steps : ℕ}
    (error : Fin steps → Ω → ℝ) (k : Fin steps) (omega : Ω) :
    Fin k.val → ℝ :=
  fun i ↦ error ⟨i.val, lt_trans i.isLt k.isLt⟩ omega

/-- Finite-computation form of Definition 1.3. The displayed integral identity
is the test-function characterization of
`E(delta_k | delta_{k-1},...,delta_1) = E(delta_k)`. -/
def p06MeanIndependent {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) {steps : ℕ}
    (error : Fin steps → Ω → ℝ) : Prop :=
  ∀ (k : Fin steps) (g : (Fin k.val → ℝ) → ℝ),
    MeasureTheory.Integrable
        (fun omega ↦ g (p06PriorErrors error k omega)) mu →
      MeasureTheory.Integrable
        (fun omega ↦
          g (p06PriorErrors error k omega) * error k omega) mu →
      (∫ omega,
          g (p06PriorErrors error k omega) * error k omega ∂mu) =
        (∫ omega, g (p06PriorErrors error k omega) ∂mu) *
          ∫ omega, error k omega ∂mu

/-- P06 Model 1.5 for a finite computation. Every generated scalar operation
obeys the standard relative-error equation (1.4); errors are ordered,
measurable, mean independent, and have mean zero. The probability measure is
not restricted to a finite sample space. -/
structure P06Model15 (Ω : Type*) [MeasurableSpace Ω] where
  probability : MeasureTheory.Measure Ω
  probability_univ : probability Set.univ = 1
  operationCount : ℕ
  exactValue : Fin operationCount → Ω → ℝ
  computedValue : Fin operationCount → Ω → ℝ
  error : Fin operationCount → Ω → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_lt_one : unitRoundoff < 1
  relative_error : ∀ k omega,
    computedValue k omega = exactValue k omega * (1 + error k omega)
  error_bound : ∀ k omega, |error k omega| ≤ unitRoundoff
  error_measurable : ∀ k, Measurable (error k)
  error_integrable : ∀ k,
    MeasureTheory.Integrable (error k) probability
  error_mean_zero : ∀ k, ∫ omega, error k omega ∂probability = 0
  error_mean_independent : p06MeanIndependent probability error

/-- The entries below the active diagonal position that the source algorithm
sets to exact zero after applying one perturbed Householder transformation. -/
noncomputable def p06HouseholderQRStep {m n : ℕ}
    (j : Fin n) (P : Fin m → Fin m → ℝ)
    (B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i k ↦ if k = j ∧ j.val < i.val then 0 else p06RectMatMul P B i k

/-- A padded Householder vector is constructed for an active column when it
has no support above the pivot and its exact reflector annihilates that
column below the pivot. Normalization is recorded separately by the run. -/
def p06HouseholderForActiveColumn {m n : ℕ}
    (j : Fin n) (x v : Fin m → ℝ) : Prop :=
  (∀ i, i.val < j.val → v i = 0) ∧
    ∀ i, j.val < i.val →
      p06MatVec (p06HouseholderMatrix v) x i = 0

/-- A Householder QR execution represented in the perturbed-transformation
form (4.1). The reflector is a deterministic construction from the current
active column, the intended subdiagonal entries are explicitly set to zero,
and every final entry is linked to the Model 1.5 scalar trace. -/
structure P06HouseholderQRRun
    (Ω : Type*) [MeasurableSpace Ω] (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (model : P06Model15 Ω) where
  rows_ge_columns : n ≤ m
  columns_pos : 0 < n
  reflectorBuilder : Fin n → (Fin m → ℝ) → Fin m → ℝ
  householderVector : Fin n → Ω → Fin m → ℝ
  localPerturbation : Fin n → Ω → Fin m → Fin m → ℝ
  state : Fin (n + 1) → Ω → Fin m → Fin n → ℝ
  RHat : Ω → Fin m → Fin n → ℝ
  exactQTransposeState : Fin (n + 1) → Ω → Fin m → Fin m → ℝ
  exactQ : Ω → Fin m → Fin m → ℝ
  outputIndex : Fin m → Fin n → Fin model.operationCount
  householder_from_active_column : ∀ j omega,
    householderVector j omega =
      reflectorBuilder j (fun i ↦ state j.castSucc omega i j)
  householder_active_column : ∀ j omega,
    p06HouseholderForActiveColumn j
      (fun i ↦ state j.castSucc omega i j) (householderVector j omega)
  householder_normalized : ∀ j omega,
    ∑ i : Fin m, householderVector j omega i ^ 2 = 2
  initial_state : ∀ omega, state 0 omega = A
  rounded_step : ∀ j omega,
    state j.succ omega =
      p06HouseholderQRStep j
        (fun i k ↦
          p06HouseholderMatrix (householderVector j omega) i k +
            localPerturbation j omega i k)
        (state j.castSucc omega)
  exactQTranspose_initial : ∀ omega,
    exactQTransposeState 0 omega = p06FiniteId
  exactQTranspose_step : ∀ j omega,
    exactQTransposeState j.succ omega =
      p06RectMatMul (p06HouseholderMatrix (householderVector j omega))
        (exactQTransposeState j.castSucc omega)
  exactQ_from_steps : ∀ omega i k,
    exactQ omega i k = exactQTransposeState (Fin.last n) omega k i
  exactQ_orthogonal : ∀ omega, p06Orthogonal (exactQ omega)
  output_state : ∀ omega, RHat omega = state (Fin.last n) omega
  output_from_trace : ∀ omega i j,
    RHat omega i j = model.computedValue (outputIndex i j) omega
  output_upper_trapezoidal : ∀ omega, p06UpperTrapezoidal (RHat omega)

/-- The probability-one strengthening of the local application bound (4.2)
assumed in Lemma 4.2 and Theorem 4.4. -/
structure P06Lemma42Assumption
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {model : P06Model15 Ω}
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Ω
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j, p06RectOpNorm2Le (run.localPerturbation j omega)
        ((c5 : ℝ) * p06GammaTilde m lambda model.unitRoundoff)
  probability_one : model.probability localEvent = 1

/-- The one-column conclusion of Lemma 4.2, specialized to a column of the QR
execution. Theorem 4.4 still has to intersect these events, assemble one
matrix perturbation, prove the simultaneous probability, and aggregate the
column bounds. -/
structure P06Lemma42ColumnCertificate
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {model : P06Model15 Ω}
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 c6 : ℕ) (lambda : ℝ)
    (hlocal : P06Lemma42Assumption run c5 lambda) (column : Fin n) where
  goodEvent : Set Ω
  goodEvent_measurable : MeasurableSet goodEvent
  goodEvent_subset_local : goodEvent ⊆ hlocal.localEvent
  failure_probability_bound :
    model.probability.real goodEventᶜ ≤
      2 * (m : ℝ) * Real.exp (-lambda ^ 2)
  deltaColumn : Ω → Fin m → ℝ
  remainder : ℝ → Ω → ℝ
  remainder_control : ∀ omega,
    P06SecondOrderControl (fun u ↦ remainder u omega) model.unitRoundoff
  exact_column_relation : ∀ omega i,
    A i column + deltaColumn omega i =
      ∑ k : Fin m, run.exactQ omega i k * run.RHat omega k column
  column_bound_on_good : ∀ omega, omega ∈ goodEvent →
    p06VecNorm2 (deltaColumn omega) ≤
      p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
          p06VecNorm2 (fun i ↦ A i column) +
        |remainder model.unitRoundoff omega|

/-- Euclidean norm on an arbitrary finite index type, needed for a dilation. -/
noncomputable def p06FiniteVecNorm2 {ι : Type*} [Fintype ι]
    (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- Matrix-vector multiplication on an arbitrary finite index type. -/
noncomputable def p06FiniteMatVec {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i ↦ ∑ j, A i j * x j

/-- Quadratic form on an arbitrary finite real matrix. -/
noncomputable def p06FiniteQuadraticForm {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, x i * p06FiniteMatVec A x i

/-- Quadratic-form (Loewner) order used to express the largest-eigenvalue
threshold in P06 equation (3.4) without introducing eigenvalue machinery. -/
def p06FiniteLoewnerLe {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) : Prop :=
  ∀ x, p06FiniteQuadraticForm A x ≤ p06FiniteQuadraticForm B x

/-- P06 equation (3.3): the symmetric dilation `[[0,M],[Mᵀ,0]]`. -/
noncomputable def p06SelfAdjointDilation {m n : ℕ}
    (M : Fin m → Fin n → ℝ) :
    (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → ℝ :=
  fun a b ↦
    match a, b with
    | Sum.inl i, Sum.inr j => M i j
    | Sum.inr j, Sum.inl i => M i j
    | _, _ => 0

/-- Entrywise asymptotic order for a finite square-matrix family. This is the
finite-dimensional interpretation of the matrix-valued `O` notation in (4.8),
without choosing a norm or a hidden constant that the paper does not specify. -/
def p06MatrixFamilyIsBigOAtZero {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ) : Prop :=
  ∀ i j, (fun u ↦ A u i j) =O[nhds 0] scale

/-- A finite square-matrix remainder of order `u²` at zero. -/
def p06MatrixSecondOrderAtZero {m : ℕ}
    (remainder : ℝ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  p06MatrixFamilyIsBigOAtZero remainder fun u ↦ u ^ 2

/-- Product `P_(k-1) ⋯ P_1 P_0`, with the empty product equal to the
identity matrix. -/
noncomputable def p06HouseholderProduct {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | k + 1 => P k * p06HouseholderProduct P k

/-- Product of the locally perturbed transformations through step `k`. -/
noncomputable def p06PerturbedHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 1
  | u, omega, k + 1 =>
      (P k + DeltaP u k omega) *
        p06PerturbedHouseholderProduct P DeltaP u omega k

/-- Sum of all product terms containing exactly one local `DeltaP_j`, in the
unfactored ordering of the first line of (4.8). -/
noncomputable def p06FirstOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega * p06HouseholderProduct P k

/-- Exact sum of all terms containing at least two local perturbations. Its
recurrence is obtained by multiplying the zero-, one-, and higher-order parts
by the next factor `P_k + DeltaP_k`. -/
noncomputable def p06HigherOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06HigherOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06HigherOrderHouseholderProduct P DeltaP u omega k

/-- Exact Householder matrices generated by a sequence of normalized vectors. -/
noncomputable def p06HouseholderSequenceMatrix {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  p06HouseholderMatrix (v j)

/-- A unit-roundoff-indexed execution family for the vector computation in
Lemmas 4.1--4.2. The distinguished execution at `model.unitRoundoff` is tied
to the Model 1.5 scalar trace; the family supplies the asymptotic meaning of
the `O(u²)` notation in (4.8). -/
structure P06HouseholderApplicationFamily
    (Omega : Type*) [MeasurableSpace Omega] (m r : ℕ)
    (model : P06Model15 Omega) where
  dimension_pos : 0 < m
  steps_pos : 0 < r
  b : Fin m → ℝ
  householderVector : ℕ → Fin m → ℝ
  localPerturbation :
    ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ
  computed : ℝ → Omega → Fin m → ℝ
  outputIndex : Fin m → Fin model.operationCount
  householder_normalized : ∀ j, j < r →
    ∑ i : Fin m, householderVector j i ^ 2 = 2
  householder_involutory : ∀ j, j < r →
    p06HouseholderSequenceMatrix householderVector j *
        p06HouseholderSequenceMatrix householderVector j = 1
  computed_product : ∀ u omega,
    computed u omega =
      p06MatVec
        (p06PerturbedHouseholderProduct
          (p06HouseholderSequenceMatrix householderVector)
          localPerturbation u omega r)
        b
  output_from_trace : ∀ omega i,
    computed model.unitRoundoff omega i =
      model.computedValue (outputIndex i) omega

/-- The probability-one form of the local application bound (4.2) used by
Lemma 4.2, together with its family-level `DeltaP_j = O(u)` meaning. -/
structure P06Lemma42VectorAssumption
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Omega
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j : Fin r,
        p06RectOpNorm2Le
          (run.localPerturbation model.unitRoundoff j.val omega)
          ((c5 : ℝ) * p06GammaTilde m lambda model.unitRoundoff)
  local_first_order : ∀ omega, omega ∈ localEvent →
    ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ run.localPerturbation u j omega) (fun u ↦ u)
  probability_one : model.probability localEvent = 1

/-- The exact transformed vector `b_(r+1) = P_r ⋯ P_1 b`. -/
noncomputable def p06ApplicationExactState
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) : Fin m → ℝ :=
  p06MatVec
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)
    run.b

/-- The zero-based form of (4.9) for an arbitrary prefix length. -/
noncomputable def p06TransformedHouseholderInsertion
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (p06HouseholderProduct P (j + 1)) *
    DeltaP u j omega * p06HouseholderProduct P j

/-- Sum of the transformed insertions with zero-based indices `0 <= j < k`. -/
noncomputable def p06TransformedHouseholderInsertionSum
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ j ∈ Finset.range k,
    p06TransformedHouseholderInsertion P DeltaP u omega j

/-- The paper's `Q = (P_r ⋯ P_1)^T`. -/
noncomputable def p06ApplicationQ
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)

/-- The unfactored sum in the first line of equation (4.8). -/
noncomputable def p06ApplicationFirstOrderMatrix
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06FirstOrderHouseholderProduct
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

/-- Equation (4.9), with zero-based `j`: the left product includes `P_j`,
while the right product ends at `P_(j-1)` and is empty when `j = 0`. -/
noncomputable def p06ApplicationF
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) (j : Fin r) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertion
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega j.val

/-- The sum `sum_(j=1)^r F_j` from the second line of (4.8). -/
noncomputable def p06ApplicationFSum
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertionSum
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

end HighamBench
