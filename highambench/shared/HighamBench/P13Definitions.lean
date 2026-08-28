import HighamBench.Core
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Sign

namespace HighamBench

open scoped BigOperators

/-- The Lagrange-form value at a fixed evaluation point, with the values of
the Lagrange basis functions supplied as `ell`. -/
noncomputable def p13InterpolationValue {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  ∑ i, ell i * f i

/-- The closed-form quotient on the right-hand side of Lemma 2.2, equation
(2.2). The lemma identifies Definition 2.1's perturbation condition number with
this quantity. -/
noncomputable def p13Condition {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  (∑ i, |ell i * f i|) / |p13InterpolationValue ell f|

/-! ## Exact Lagrange interpolation condition number -/

/-- Fixed data for the degree-`n` interpolation problem in Section 2. There
are exactly `n+1` pairwise distinct nodes, while the evaluation point and nodes
remain fixed under perturbations of `data`. -/
structure P13LagrangeProblem (n : ℕ) where
  nodes : Fin (n + 1) → ℝ
  data : Fin (n + 1) → ℝ
  x : ℝ
  nodes_injective : Function.Injective nodes

/-- The Lagrange basis value `ell_j(x)` from equation (2.1). The skipped
`k = j` factors are represented by `1`. -/
noncomputable def p13LagrangeBasis {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (x : ℝ) (j : Fin (n + 1)) : ℝ :=
  (∏ k : Fin (n + 1), if k = j then 1 else x - nodes k) /
    (∏ k : Fin (n + 1), if k = j then 1 else nodes j - nodes k)

/-- All Lagrange basis values at the fixed evaluation point. -/
noncomputable def p13LagrangeBasisValues {n : ℕ}
    (problem : P13LagrangeProblem n) : Fin (n + 1) → ℝ :=
  p13LagrangeBasis problem.nodes problem.x

/-- The exact degree-`n` interpolant value `p_f(x)` from equation (2.1). -/
noncomputable def p13LagrangeValue {n : ℕ}
    (problem : P13LagrangeProblem n) : ℝ :=
  p13InterpolationValue (p13LagrangeBasisValues problem) problem.data

/-- Definition 2.1's componentwise relative data perturbation
`|delta f| <= epsilon |f|`. -/
def p13DataPerturbation {m : ℕ} (f deltaF : Fin m → ℝ)
    (epsilon : ℝ) : Prop :=
  ∀ j, |deltaF j| ≤ epsilon * |f j|

/-- Relative change in the exact interpolation value caused by `deltaF`.
Definition 2.1 excludes a zero unperturbed value. -/
noncomputable def p13RelativeInterpolationChange {m : ℕ}
    (ell f deltaF : Fin m → ℝ) : ℝ :=
  |p13InterpolationValue ell f - p13InterpolationValue ell (f + deltaF)| /
    |p13InterpolationValue ell f|

/-- The set inside Definition 2.1's supremum at a fixed positive radius. Each
element is the relative output change divided by that radius. -/
def p13ScaledPerturbationSet {m : ℕ} (ell f : Fin m → ℝ)
    (epsilon : ℝ) : Set ℝ :=
  {q | ∃ deltaF : Fin m → ℝ,
    p13DataPerturbation f deltaF epsilon ∧
      q = p13RelativeInterpolationChange ell f deltaF / epsilon}

/-- Definition 2.1's supremum at perturbation radius `epsilon`. -/
noncomputable def p13PerturbationSupremum {m : ℕ}
    (ell f : Fin m → ℝ) (epsilon : ℝ) : ℝ :=
  sSup (p13ScaledPerturbationSet ell f epsilon)

/-- A scalar is Definition 2.1's condition number when the perturbation
suprema tend to it through positive radii. This `Tendsto` formulation records
the equality asserted by the paper without choosing a value for a nonexistent
limit outside the nonzero-value domain. -/
def p13IsComponentwiseConditionNumber {m : ℕ}
    (ell f : Fin m → ℝ) (condition : ℝ) : Prop :=
  Filter.Tendsto (p13PerturbationSupremum ell f)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds condition)

/-- The exact second barycentric formula, with `coeff i = w_i/(x-x_i)`. -/
noncomputable def p13BarycentricValue {n : ℕ}
    (coeff f : Fin n → ℝ) : ℝ :=
  p13InterpolationValue coeff f / p13InterpolationValue coeff (fun _ => 1)

/-- A finite certificate for a computed second barycentric formula: the
numerator terms and denominator terms receive separate additive errors. -/
noncomputable def p13BarycentricComputed {n : ℕ}
    (coeff f deltaNum deltaDen : Fin n → ℝ) : ℝ :=
  (∑ i, (coeff i * f i + deltaNum i)) /
    (∑ i, (coeff i + deltaDen i))

/-- Componentwise relative perturbation of a finite family of terms. -/
def p13TermPerturbation {n : ℕ}
    (v delta : Fin n → ℝ) (epsilon : ℝ) : Prop :=
  ∀ i, |delta i| ≤ epsilon * |v i|

/-! ## The second barycentric formula and its rounding-error execution -/

/-- The reciprocal-product weight (3.2), with the omitted `k = j` factor
represented by `1`. -/
noncomputable def p13DirectBarycentricWeight {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∏ k : Fin (n + 1), if k = j then 1 else nodes j - nodes k)⁻¹

/-- The coefficient `w_j / (x - x_j)` in the second barycentric formula. -/
noncomputable def p13DirectBarycentricCoefficient {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (x : ℝ) (j : Fin (n + 1)) : ℝ :=
  p13DirectBarycentricWeight nodes j / (x - nodes j)

/-- Fixed data for equation (4.1). The real fields are the exact values of the
paper's floating-point inputs; the source does not specify a concrete format. -/
structure P13SecondBarycentricProblem (n : ℕ) where
  nodes : Fin (n + 1) → ℝ
  data : Fin (n + 1) → ℝ
  x : ℝ
  nodes_injective : Function.Injective nodes
  evaluation_off_nodes : ∀ j, x ≠ nodes j

/-- Number of local errors inherited from direct weight computation. -/
def p13WeightCounterLength (n : ℕ) : ℕ := 2 * n

/-- Number of local errors in each numerator term and its summation. -/
def p13NumeratorEvaluationCounterLength (n : ℕ) : ℕ := n + 3

/-- Number of local errors in each denominator term and its summation. -/
def p13DenominatorEvaluationCounterLength (n : ℕ) : ℕ := n + 2

/-- Collected numerator counter in the exact expression before Theorem 4.1. -/
def p13NumeratorCounterLength (n : ℕ) : ℕ := 3 * n + 4

/-- Collected denominator counter in the exact expression before Theorem 4.1. -/
def p13DenominatorCounterLength (n : ℕ) : ℕ := 3 * n + 2

/-- A literal Higham relative-error counter: every local factor is either
`1 + delta` or its reciprocal, and the standard `gamma_k` consequence is
carried as the inherited error-counter lemma used by the paper. -/
structure P13RelativeErrorCounter (u : ℝ) (k : ℕ) where
  value : ℝ
  localError : Fin k → ℝ
  reciprocal : Fin k → Bool
  localError_le : ∀ i, |localError i| ≤ u
  value_eq :
    value = ∏ i, if reciprocal i then (1 + localError i)⁻¹ else 1 + localError i
  gamma_le : GammaValid u k → |value - 1| ≤ gamma u k

/-- A source-level execution certificate for the second barycentric formula.
It retains the shared weight errors, the two evaluation counters, the final
division error, and the two collected counters printed before Theorem 4.1. -/
structure P13SecondBarycentricExecution {n : ℕ}
    (problem : P13SecondBarycentricProblem n) (u : ℝ) where
  u_nonneg : 0 ≤ u
  weightCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13WeightCounterLength n)
  numeratorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13DenominatorEvaluationCounterLength n)
  quotientCounter : P13RelativeErrorCounter u 1
  numeratorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13NumeratorCounterLength n)
  denominatorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13DenominatorCounterLength n)
  weightGammaValid : GammaValid u (p13WeightCounterLength n)
  numeratorEvaluationGammaValid :
    GammaValid u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationGammaValid :
    GammaValid u (p13DenominatorEvaluationCounterLength n)
  quotientGammaValid : GammaValid u 1
  numeratorGammaValid : GammaValid u (p13NumeratorCounterLength n)
  denominatorGammaValid : GammaValid u (p13DenominatorCounterLength n)
  numeratorCounter_eq : ∀ j : Fin (n + 1),
    (numeratorCounter j).value =
      (weightCounter j).value * (numeratorEvaluationCounter j).value *
        quotientCounter.value
  denominatorCounter_eq : ∀ j : Fin (n + 1),
    (denominatorCounter j).value =
      (weightCounter j).value * (denominatorEvaluationCounter j).value

/-- Exact numerator in (4.1). -/
noncomputable def p13SecondBarycentricNumerator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

/-- Exact denominator in (4.1), equivalently the constant-one interpolation
sum used in `cond(x,n,1)`. -/
noncomputable def p13SecondBarycentricDenominator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

/-- Exact value of the second barycentric formula (4.1). -/
noncomputable def p13SecondBarycentricExact {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13SecondBarycentricNumerator problem /
    p13SecondBarycentricDenominator problem

/-- The computed quotient in the paper's uncollected counter form. -/
noncomputable def p13SecondBarycentricComputed {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  ((∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) /
    (∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value *
          (run.denominatorEvaluationCounter j).value)) *
    run.quotientCounter.value

/-- Relative forward error used by Theorem 4.1. -/
noncomputable def p13SecondBarycentricRelativeError {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  |p13SecondBarycentricExact problem - p13SecondBarycentricComputed run| /
    |p13SecondBarycentricExact problem|

/-- The data condition number in Theorem 4.1. -/
noncomputable def p13SecondBarycentricDataCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

/-- The denominator-cancellation condition number `cond(x,n,1)`. -/
noncomputable def p13SecondBarycentricOneCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

/-- Exact finite envelope obtained from the two collected gamma counters. -/
noncomputable def p13SecondBarycentricFiniteEnvelope
    (n : ℕ) (u conditionData conditionOne : ℝ) : ℝ :=
  (gamma u (p13NumeratorCounterLength n) * conditionData +
      gamma u (p13DenominatorCounterLength n) * conditionOne) /
    (1 - gamma u (p13DenominatorCounterLength n) * conditionOne)

/-- The two printed first-order coefficients in equation (4.3), without the
factor `u`. -/
noncomputable def p13SecondBarycentricFirstOrderCoefficient
    (n : ℕ) (conditionData conditionOne : ℝ) : ℝ :=
  (p13NumeratorCounterLength n : ℝ) * conditionData +
    (p13DenominatorCounterLength n : ℝ) * conditionOne

/-- The explicit quadratic-and-higher remainder hidden by `O(u^2)` in (4.3).
The denominator is nonzero in a neighborhood of zero. -/
noncomputable def p13SecondBarycentricForwardRemainder
    (n : ℕ) (conditionData conditionOne u : ℝ) : ℝ :=
  let p : ℝ := p13NumeratorCounterLength n
  let q : ℝ := p13DenominatorCounterLength n
  let A : ℝ := p * conditionData
  let B : ℝ := q * conditionOne
  u ^ 2 *
      (A * p + B * q + A * B + B ^ 2 -
        (A + B) * p * (q + B) * u) /
    ((1 - p * u) * (1 - (q + B) * u))

/-! ## First-order sharpness -/

/-- A realizable first-order counter direction: it is the sum of `k` local
rounding directions, each of magnitude at most one. -/
structure P13FirstOrderCounterDirection (k : ℕ) where
  localDirection : Fin k → ℝ
  localDirection_le_one : ∀ i, |localDirection i| ≤ 1

/-- Total first-order coefficient of a relative-error counter direction. -/
noncomputable def p13FirstOrderCounterDirectionValue {k : ℕ}
    (direction : P13FirstOrderCounterDirection k) : ℝ :=
  ∑ i, direction.localDirection i

/-- Linearized relative forward error of the same four counter stages used by
the exact execution certificate. -/
noncomputable def p13SecondBarycentricFirstOrderResponse {n : ℕ}
    (problem : P13SecondBarycentricProblem n)
    (weightDirection :
      ∀ _j : Fin (n + 1),
        P13FirstOrderCounterDirection (p13WeightCounterLength n))
    (numeratorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13NumeratorEvaluationCounterLength n))
    (denominatorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13DenominatorEvaluationCounterLength n))
    (quotientDirection : P13FirstOrderCounterDirection 1) : ℝ :=
  let coeff := p13DirectBarycentricCoefficient problem.nodes problem.x
  |(∑ j, coeff j * problem.data j *
        (p13FirstOrderCounterDirectionValue (weightDirection j) +
          p13FirstOrderCounterDirectionValue (numeratorDirection j))) /
      p13SecondBarycentricNumerator problem -
    (∑ j, coeff j *
        (p13FirstOrderCounterDirectionValue (weightDirection j) +
          p13FirstOrderCounterDirectionValue (denominatorDirection j))) /
      p13SecondBarycentricDenominator problem +
    p13FirstOrderCounterDirectionValue quotientDirection|

/-- Formal content of the paper's sharpness sentence: realizable local error
directions attain at least one third of the displayed leading coefficient. -/
def P13SecondBarycentricFirstOrderSharp {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : Prop :=
  ∃ (weightDirection :
      ∀ _j : Fin (n + 1),
        P13FirstOrderCounterDirection (p13WeightCounterLength n))
    (numeratorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13NumeratorEvaluationCounterLength n))
    (denominatorDirection :
      ∀ _j : Fin (n + 1), P13FirstOrderCounterDirection
        (p13DenominatorEvaluationCounterLength n))
    (quotientDirection : P13FirstOrderCounterDirection 1),
    (1 / 3 : ℝ) *
        p13SecondBarycentricFirstOrderCoefficient n
          (p13SecondBarycentricDataCondition problem)
          (p13SecondBarycentricOneCondition problem) ≤
      p13SecondBarycentricFirstOrderResponse problem weightDirection
        numeratorDirection denominatorDirection quotientDirection

end HighamBench
