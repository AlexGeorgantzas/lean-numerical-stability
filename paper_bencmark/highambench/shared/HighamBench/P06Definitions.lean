import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.ConditionalExpectation

namespace HighamBench

open MeasureTheory

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

/-- Euclidean norm in the finite real-vector notation used by P06. -/
noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Rectangular Frobenius norm in P06's finite matrix notation. -/
noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Rectangular matrix-vector multiplication. -/
noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The homogeneous rectangular operator-2 upper-bound predicate. -/
def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

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

/-- Identity matrix on an arbitrary finite decidable index type. -/
noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

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

/-- P06 equation (1.1), the standard deterministic product constant. -/
noncomputable def p06Gamma (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) * u / (1 - (n : ℝ) * u)

/-- P06 equation (1.6), the probabilistic product constant. -/
noncomputable def p06ProbGamma (n : ℕ) (u lambdaParam : ℝ) : ℝ :=
  Real.exp
    ((lambdaParam * Real.sqrt (n : ℝ) * u + (n : ℝ) * u ^ 2) / (1 - u)) - 1

/-- The success-probability expression attached to Lemma 1.4. -/
noncomputable def p06ProductSuccessProbability (lambdaParam : ℝ) : ℝ :=
  1 - 2 * Real.exp (-(lambdaParam ^ 2) / 2)

/-- Pointwise matrix addition in the finite rectangular notation of P06. -/
def p06MatAdd {m n : ℕ} (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

/-- Pointwise matrix subtraction in the finite rectangular notation of P06. -/
def p06MatSub {m n : ℕ} (A B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

/-- Scalar multiplication of a finite rectangular matrix. -/
def p06MatScale {m n : ℕ} (c : ℝ) (A : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ c * A i j

/-- Transpose of a finite rectangular matrix. -/
def p06Transpose {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin m → ℝ :=
  fun j i ↦ A i j

/-- Product of finite rectangular matrices. -/
noncomputable def p06MatMul {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin r → ℝ) :
    Fin m → Fin r → ℝ :=
  fun i k ↦ ∑ j : Fin n, A i j * B j k

/-- Finite identity matrix. -/
noncomputable def p06IdMatrix {n : ℕ} : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

/-- Orthogonality in P06's finite real-matrix notation. -/
def p06Orthogonal {n : ℕ} (Q : Fin n → Fin n → ℝ) : Prop :=
  p06MatMul (p06Transpose Q) Q = p06IdMatrix ∧
    p06MatMul Q (p06Transpose Q) = p06IdMatrix

/-- Upper-trapezoidal support for an m-by-n matrix. -/
def p06UpperTrapezoidal {m n : ℕ} (R : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

/-- P06's normalized Householder matrix I - v v-transpose. -/
noncomputable def p06Householder {m : ℕ} (v : Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j ↦ p06IdMatrix i j - v i * v j

/-- Columnwise relative backward-error predicate used in (1.2), (4.15),
(4.17), and (4.21). -/
def p06ColumnwiseRelativeError {m n : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (η : ℝ) : Prop :=
  ∀ j, p06VecNorm2 (fun i ↦ ΔA i j) ≤ η * p06VecNorm2 (fun i ↦ A i j)

/-- Exact first-order matrix perturbation envelope a*u + O(u^2), represented
without silently replacing the paper's asymptotic remainder by equality. -/
def p06FirstOrderEnvelope (value leading u : ℝ) : Prop :=
  ∃ remainderConstant : ℝ, 0 ≤ remainderConstant ∧
    value ≤ leading * u + remainderConstant * u ^ 2

/-- A finite weighted QR backward-error candidate from equation (6.1). -/
noncomputable def p06WeightedQRError {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (Q : Fin m → Fin m → ℝ)
    (d : Fin n → ℝ) : ℝ :=
  p06FrobNorm (fun i j ↦ (A i j - p06MatMul Q B i j) * d j)

/-- Mathematical content of the minimum in equation (6.1): a value is the
weighted QR backward error precisely when it is attained by an orthogonal
factor and is no larger than every other orthogonal candidate. -/
def p06IsWeightedQRMinimum {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) (d : Fin n → ℝ) (μ : ℝ) : Prop :=
  (∃ Q, p06Orthogonal Q ∧ μ = p06WeightedQRError A B Q d) ∧
    ∀ Q, p06Orthogonal Q → μ ≤ p06WeightedQRError A B Q d


/-- A source-facing event-probability lower bound using an actual Mathlib
measure rather than an unconstrained probability oracle. -/
def p06ProbabilityAtLeast {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (event : Ω → Prop) (lower : ℝ) : Prop :=
  ENNReal.ofReal lower ≤ mu {omega | event omega}

/-- The sigma-algebra generated by the rounding errors preceding index k. -/
noncomputable def p06RoundingHistory {Ω : Type*} [MeasurableSpace Ω]
    (delta : ℕ → Ω → ℝ) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ i : Fin k, MeasurableSpace.comap (delta i) (borel ℝ)

/-- P06 Definition 1.3, expressed with Mathlib conditional expectation:
for indices after the first, conditioning on all earlier errors does not
change the expectation.  The generated history is required to be a genuine
sub-sigma-algebra of the ambient measurable space; this makes the condition
independent of null-set representatives of the random variables. -/
def p06MeanIndependent {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (n : ℕ) (delta : ℕ → Ω → ℝ) : Prop :=
  (∀ k, k < n → p06RoundingHistory delta k ≤ ‹MeasurableSpace Ω›) ∧
    ∀ k, 0 < k → k < n →
      mu[delta k | p06RoundingHistory delta k] =ᵐ[mu]
        fun _ ↦ ∫ omega, delta k omega ∂mu

/-- P06 Model 1.5: the ordered errors obey the elementary bound, are
integrable and mean independent, and have mean zero. -/
def p06RoundingErrorModel {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (n : ℕ) (u : ℝ) (delta : ℕ → Ω → ℝ) : Prop :=
  (∀ k, k < n → ∀ᵐ omega ∂mu, |delta k omega| ≤ u) ∧
    (∀ k, k < n → Integrable (delta k) mu) ∧
    p06MeanIndependent mu n delta ∧
    ∀ k, k < n → ∫ omega, delta k omega ∂mu = 0

/-- Symmetry for a finite real square matrix. -/
def p06Symmetric {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, A i j = A j i

/-- The event that a symmetric matrix has a Rayleigh quotient at least t,
an eigenvalue-free presentation of lambda_max(A) >= t. -/
def p06LambdaMaxGe {n : ℕ} (A : Fin n → Fin n → ℝ) (t : ℝ) : Prop :=
  ∃ x : Fin n → ℝ,
    p06FiniteVecNorm2 x = 1 ∧ t ≤ p06FiniteQuadraticForm A x

/-- Pointwise sum of a finite sequence of square matrices. -/
noncomputable def p06MatrixSum {r n : ℕ}
    (A : Fin r → Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin r, A k i j

/-- Pointwise sum of a finite sequence of rectangular matrices. -/
noncomputable def p06RectMatrixSum {r m n : ℕ}
    (A : Fin r → Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin r, A k i j

/-- Square of a finite square matrix. -/
noncomputable def p06MatrixSquare {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  p06MatMul A A

/-- One factor in the signed product of Lemmas 1.2 and 1.4. -/
noncomputable def p06SignedFactor (delta : ℝ) (positiveExponent : Bool) : ℝ :=
  if positiveExponent then 1 + delta else (1 + delta)⁻¹

/-- The signed product appearing in equations (1.5) and (1.7). -/
noncomputable def p06SignedProduct {n : ℕ}
    (delta : Fin n → ℝ) (positiveExponent : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, p06SignedFactor (delta i) (positiveExponent i)

/-- The paper's sign convention: negative inputs map to -1 and zero and
positive inputs map to 1. -/
noncomputable def p06Sign (x : ℝ) : ℝ := if x < 0 then -1 else 1

/-- The scalar and vector produced by the Householder construction in
Lemma 2.2, before floating-point perturbations are introduced. -/
noncomputable def p06HouseholderConstruction {n : ℕ} [NeZero n]
    (x : Fin n → ℝ) : ℝ × (Fin n → ℝ) :=
  let s := p06Sign (x 0) * p06VecNorm2 x
  let v := Function.update x 0 (x 0 + s)
  (1 / (s * v 0), v)

/-- A source-order state transition for applying a supplied sequence of
Householder matrices to a rectangular matrix. -/
noncomputable def p06HouseholderMatrixState {m n : ℕ}
    (P : ℕ → Fin m → Fin m → ℝ) (A : Fin m → Fin n → ℝ) :
    ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 => p06MatMul (P k) (p06HouseholderMatrixState P A k)

/-- The compact WY matrix update B <- B + W(Y-transpose B) from section 5.2. -/
noncomputable def p06WYUpdate {m b n : ℕ}
    (W Y : Fin m → Fin b → ℝ)
    (B : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  p06MatAdd B (p06MatMul W (p06MatMul (p06Transpose Y) B))



/-- The subordinate 2-norm as the infimum of all nonnegative homogeneous
upper bounds. This avoids an extra finite-dimensional operator-norm API while
preserving the paper's norm semantics. -/
noncomputable def p06OperatorNorm2 {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  sInf {L : ℝ | 0 ≤ L ∧ p06RectOpNorm2Le A L}

/-- Positive semidefiniteness in quadratic-form order. -/
def p06PositiveSemidefinite {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  p06FiniteLoewnerLe (fun _ _ ↦ 0) A

/-- The sigma-algebra generated componentwise by all random matrices preceding
index k. -/
noncomputable def p06MatrixHistory {Omega : Type*} [MeasurableSpace Omega]
    {ι : Type*} [Fintype ι]
    (X : ℕ → Omega → ι → ι → ℝ) (k : ℕ) :
    MeasurableSpace Omega :=
  ⨆ i : Fin k, ⨆ p : ι × ι,
    MeasurableSpace.comap (fun omega ↦ X i omega p.1 p.2) (borel ℝ)

/-- Componentwise conditional-mean-zero hypothesis used by Theorem 3.1.
Each generated history is required to be a genuine sub-sigma-algebra of the
ambient measurable space, so conditional expectation cannot become vacuous
because of a nonmeasurable null-set representative. -/
def p06MatrixConditionalMeanZero {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {ι : Type*} [Fintype ι]
    (X : ℕ → Omega → ι → ι → ℝ) (r : ℕ) : Prop :=
  (∀ k, k < r → p06MatrixHistory X k ≤ ‹MeasurableSpace Omega›) ∧
    ∀ k, k < r → ∀ i j,
      mu[(fun omega ↦ X k omega i j) | p06MatrixHistory X k] =ᵐ[mu]
        fun _ ↦ 0

/-- A polar factor in the sense recalled before Theorem 6.1. -/
def p06IsPolarFactor {n : ℕ}
    (U C : Fin n → Fin n → ℝ) : Prop :=
  p06Orthogonal U ∧
    ∃ H : Fin n → Fin n → ℝ,
      p06Symmetric H ∧ p06PositiveSemidefinite H ∧
        C = p06MatMul U H

/-- A finite diagonal matrix. -/
noncomputable def p06DiagonalMatrix {n : ℕ}
    (d : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then d i else 0


/-- A finite QR factorization with the paper's square orthogonal factor and
upper-trapezoidal factor. -/
def p06QRFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin m → ℝ)
    (R : Fin m → Fin n → ℝ) : Prop :=
  p06Orthogonal Q ∧ p06UpperTrapezoidal R ∧ A = p06MatMul Q R

/-- The general Householder matrix I - 2*v*v-transpose/(v-transpose*v)
from the introduction. -/
noncomputable def p06GeneralHouseholder {m : ℕ}
    (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ p06IdMatrix i j -
    (2 / (∑ k : Fin m, v k ^ 2)) * v i * v j

/-- Exact elementary-operation instance of equation (1.4). -/
def p06ElementaryRoundoff (exact computed delta u : ℝ) : Prop :=
  computed = exact * (1 + delta) ∧ |delta| ≤ u

/-- Append one column pair in the compact WY recurrence of section 5.2. -/
def p06WYColumnStep {m : ℕ}
    (W Y : List (Fin m → ℝ)) (v transformedV : Fin m → ℝ) :
    List (Fin m → ℝ) × List (Fin m → ℝ) :=
  (W ++ [fun i ↦ -v i], Y ++ [transformedV])

/-- The exact numeric controls stated for all section 7 experiments. -/
structure p06ExperimentControls where
  lambdaParameter : ℝ
  dimensionIndependentConstant : ℝ
  workingPrecisionBits : ℕ
  backwardErrorPrecisionBits : ℕ
  samplesPerDimensionPair : ℕ
  roundToNearest : Bool

/-- Section 7's shared experiment controls: lambda=1, constants=1, IEEE
single working precision, double precision error evaluation, ten samples,
and round to nearest. -/
def p06Section7Controls : p06ExperimentControls where
  lambdaParameter := 1
  dimensionIndependentConstant := 1
  workingPrecisionBits := 24
  backwardErrorPrecisionBits := 53
  samplesPerDimensionPair := 10
  roundToNearest := true

/-- The exact reported SuiteSparse selection and retained counts. -/
def p06SuiteSparseCounts : ℕ × ℕ := (842, 774)

/-- The paper's heuristic square-root relation, retained as a proposition
without promoting its epistemic status to a theorem. -/
def p06SquareRootScalingHeuristic (worst probabilistic : ℝ) : Prop :=
  probabilistic ^ 2 = worst


/-- Actual nested two-sided transformation order from equation (5.1). -/
noncomputable def p06TwoSidedState {n : ℕ}
    (P : ℕ → Fin n → Fin n → ℝ) (A : Fin n → Fin n → ℝ) :
    ℕ → Fin n → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      p06MatMul (P k) (p06MatMul (p06TwoSidedState P A k)
        (p06Transpose (P k)))

/-- A finite real singular value decomposition certificate. -/
def p06IsSingularValueDecomposition {n : ℕ}
    (C U V : Fin n → Fin n → ℝ) (singularValues : Fin n → ℝ) : Prop :=
  p06Orthogonal U ∧ p06Orthogonal V ∧
    (∀ i, 0 ≤ singularValues i) ∧
    C = p06MatMul
      (p06MatMul U (p06DiagonalMatrix singularValues))
      (p06Transpose V)


end HighamBench
