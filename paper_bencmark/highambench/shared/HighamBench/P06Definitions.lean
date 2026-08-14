import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-- A Householder QR execution represented in the perturbed-transformation
form (4.1). Each final entry is linked to the Model 1.5 scalar trace, while the
state recurrence records the local matrices `Delta P_j`. -/
structure P06HouseholderQRRun
    (Ω : Type*) [MeasurableSpace Ω] (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (model : P06Model15 Ω) where
  rows_ge_columns : n ≤ m
  columns_pos : 0 < n
  householderVector : Fin n → Ω → Fin m → ℝ
  localPerturbation : Fin n → Ω → Fin m → Fin m → ℝ
  state : Fin (n + 1) → Ω → Fin m → Fin n → ℝ
  RHat : Ω → Fin m → Fin n → ℝ
  outputIndex : Fin m → Fin n → Fin model.operationCount
  householder_normalized : ∀ j omega,
    ∑ i : Fin m, householderVector j omega i ^ 2 = 2
  initial_state : ∀ omega, state 0 omega = A
  rounded_step : ∀ j omega,
    state j.succ omega =
      p06RectMatMul
        (fun i k ↦
          p06HouseholderMatrix (householderVector j omega) i k +
            localPerturbation j omega i k)
        (state j.castSucc omega)
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

/-- The simultaneous columnwise conclusion (4.16)--(4.17) supplied by
Theorem 4.4. Keeping this certificate separate makes P06-T1 exactly the next
sentence of the paper: aggregate this same event into equation (4.20). -/
structure P06Theorem44ColumnwiseCertificate
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {model : P06Model15 Ω}
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 c6 : ℕ) (lambda : ℝ)
    (_local : P06Lemma42Assumption run c5 lambda) where
  goodEvent : Set Ω
  goodEvent_measurable : MeasurableSet goodEvent
  probability_bound :
    p06P4 lambda m n ≤ ENNReal.toReal (model.probability goodEvent)
  Q : Ω → Fin m → Fin m → ℝ
  DeltaA : Ω → Fin m → Fin n → ℝ
  columnRemainder : Fin n → ℝ → Ω → ℝ
  columnRemainder_second_order : ∀ j omega,
    p06SecondOrderAtZero (fun u ↦ columnRemainder j u omega)
  orthogonal_on_good : ∀ omega, omega ∈ goodEvent →
    p06Orthogonal (Q omega)
  factorization_on_good : ∀ omega, omega ∈ goodEvent →
    A + DeltaA omega = p06RectMatMul (Q omega) (run.RHat omega)
  column_bound_on_good : ∀ omega, omega ∈ goodEvent → ∀ j,
    p06VecNorm2 (fun i ↦ DeltaA omega i j) ≤
      p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
          p06VecNorm2 (fun i ↦ A i j) +
        |columnRemainder j model.unitRoundoff omega|

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

/-- The exact state obtained after the first `r` unperturbed transformations.
The recurrence represents `P_(r-1) ⋯ P_0 b`. -/
noncomputable def p06ExactState {m : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 => p06MatVec (P r) (p06ExactState P b r)

/-- The coefficient of the terms containing exactly one local perturbation.
This is the recursive form of the insertion sum in P06 equations (4.8)--(4.9). -/
noncomputable def p06FirstOrderState {m : ℕ}
    (P E : ℕ → Fin m → Fin m → ℝ) (b : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06FirstOrderState P E b r) i +
        p06MatVec (E r) (p06ExactState P b r) i

/-- The sum of all terms containing at least two local perturbations, after
factoring out `t²` from transformations `P_r + t E_r`. -/
noncomputable def p06HigherOrderState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => fun _ ↦ 0
  | r + 1 => fun i ↦
      p06MatVec (P r) (p06HigherOrderState t P E b r) i +
        p06MatVec (E r) (p06FirstOrderState P E b r) i +
        t * p06MatVec (E r) (p06HigherOrderState t P E b r) i

/-- State obtained from the fully perturbed sequence `P_r + t E_r`. -/
noncomputable def p06PerturbedState {m : ℕ}
    (t : ℝ) (P E : ℕ → Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => b
  | r + 1 =>
      p06MatVec (fun i j ↦ P r i j + t * E r i j)
        (p06PerturbedState t P E b r)

end HighamBench
