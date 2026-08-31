import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option genSizeOf false

/-!
# HighamBench P01 definitions

This file contains the paper-specific transparent models, algorithms, reports,
and other statement-facing definitions required by the P01 benchmark tasks.
It contains no proof-bearing result declarations.
-/

namespace HighamBench

open scoped BigOperators

/-- The P01-local rounded-addition model used by its summation statements. -/
structure P01StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

attribute [simp] P01StandardAddModel.fl_add_zero

/-- P01's accumulated-error number `γₙ = n*u/(1-n*u)`. -/
noncomputable def p01Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

/-- Positivity condition for the denominator of `p01Gamma`. -/
def P01GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- P01-local left-to-right recursive summation. -/
noncomputable def p01RecursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      flAdd
        (p01RecursiveSum flAdd n (fun i => v i.castSucc))
        (v (Fin.last n))

/-- The weaker addition rule used when the arithmetic has no guard digit. -/
structure NoGuardAddModel where
  u : ℝ
  u_pos : 0 < u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ α β : ℝ,
      |α| ≤ u ∧
      |β| ≤ u ∧
      fl_add x y = x * (1 + α) + y * (1 + β)

attribute [simp] NoGuardAddModel.fl_add_zero

/-- Embed an index into the left half of a vector of length `2^(r+1)`. -/
def leftIndex (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val, by
    have hi := i.isLt
    simp [pow_succ]
    omega⟩

/-- Embed an index into the right half of a vector of length `2^(r+1)`. -/
def rightIndex (r : ℕ) (i : Fin (2 ^ r)) : Fin (2 ^ (r + 1)) :=
  ⟨i.val + 2 ^ r, by
    have hi := i.isLt
    simp [pow_succ]
    omega⟩

/-- Balanced pairwise summation of exactly `2^r` inputs. -/
noncomputable def pairwiseSum (flAdd : ℝ → ℝ → ℝ) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, v => v ⟨0, by simp⟩
  | r + 1, v =>
      flAdd
        (pairwiseSum flAdd r (fun i => v (leftIndex r i)))
        (pairwiseSum flAdd r (fun i => v (rightIndex r i)))

/-- The right side of Higham (1993), equation (5.3), without the leading `u`.

For inputs `x₁, ..., xₙ`, this is

`(|Ŝ₁| + |x₂|) + ... + (|Ŝₙ₋₁| + |xₙ|)`,

where `Ŝₖ` is the computed recursive sum of the first `k` inputs. The
recursive definition follows the same last-step split as `p01RecursiveSum`. -/
noncomputable def noGuardRecursiveRunningBudget (fp : NoGuardAddModel) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if n = 0 then
        0
      else
        noGuardRecursiveRunningBudget fp n (fun i => v i.castSucc) +
          |p01RecursiveSum fp.fl_add n (fun i => v i.castSucc)| +
          |v (Fin.last n)|

/-- Syntactic distinction noted between equations (5.3) and (2.8): the
first computed prefix in (5.3) is identified with `x₁`, while (2.8) starts
with later computed prefixes. -/
structure P01Equation53FirstComputedPrefixComparisonReport where
  equation53ContainsFirstComputedPrefixTerm : Bool
  firstComputedPrefixIdentifiedWithX1 : Bool
  equation28ContainsFirstComputedPrefixTerm : Bool

def p01Equation53FirstComputedPrefixComparisonReport :
    P01Equation53FirstComputedPrefixComparisonReport :=
  { equation53ContainsFirstComputedPrefixTerm := true
    firstComputedPrefixIdentifiedWithX1 := true
    equation28ContainsFirstComputedPrefixTerm := false }

/-! ## Source objects and arithmetic models -/

/-- The four arithmetic operations occurring in equation (1.2). -/
inductive P01BinaryOp
  | add | sub | mul | div

/-- Exact real interpretation of the operations in equation (1.2). -/
noncomputable def p01ExactOp : P01BinaryOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)

/-- Domain on which each exact arithmetic operation in (1.2) is mathematically defined. -/
def P01BinaryOpAdmissible (op : P01BinaryOp) (_x y : ℝ) : Prop :=
  match op with
  | .div => y ≠ 0
  | _ => True

/-- The full standard arithmetic model printed as equation (1.2). -/
structure P01StandardOpModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl : P01BinaryOp → ℝ → ℝ → ℝ
  model :
    ∀ op x y, P01BinaryOpAdmissible op x y → ∃ δ : ℝ,
      |δ| ≤ u ∧ fl op x y = p01ExactOp op x y * (1 + δ)

/-- Explicit scope restriction stated immediately after the standard model. -/
structure P01ArithmeticScopeReport where
  floatingPointUnderflowAssumedAbsent : Bool

def p01ArithmeticScopeReport : P01ArithmeticScopeReport :=
  { floatingPointUnderflowAssumedAbsent := true }

/-- The first coordinate in the `i`th Rosenbrock pair, using zero-based Lean indices. -/
def p01RosenbrockLeftIndex (m : ℕ) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val, by omega⟩

/-- The second coordinate in the `i`th Rosenbrock pair. -/
def p01RosenbrockRightIndex (m : ℕ) (i : Fin m) : Fin (2 * m) :=
  ⟨2 * i.val + 1, by omega⟩

/-- Read `x_i` from an `n`-entry Lean vector using the paper's one-based
coordinate convention. The fallback is irrelevant for indices `1, ..., n`. -/
def p01OneBasedValue {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : 1 ≤ i ∧ i ≤ n then x ⟨i - 1, by omega⟩ else 0

/-- The extended Rosenbrock function exactly as printed in equation (1.1). -/
noncomputable def p01ExtendedRosenbrock
    (n : ℕ) (_hn : Even n) (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2),
    ((100 : ℝ) *
        (p01OneBasedValue x (2 * i) -
          p01OneBasedValue x (2 * i - 1) ^ 2) ^ 2 +
      (1 - p01OneBasedValue x (2 * i - 1)) ^ 2)

/-- A four-entry vector, used for the symmetry following equation (1.1). -/
def p01Four (a b c d : ℝ) : Fin 4 → ℝ := ![a, b, c, d]

/-- The coordinate permutation that exchanges the two Rosenbrock pairs. -/
def p01RosenbrockPairSwapIndex : Fin 4 → Fin 4 :=
  ![⟨2, by omega⟩, ⟨3, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]

/-- The actual coordinate derivatives of the `n = 4` extended Rosenbrock
function, obtained by differentiating each one-coordinate slice. -/
noncomputable def p01ExtendedRosenbrockCoordinateDerivatives4
    (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun j =>
    deriv
      (fun t => p01ExtendedRosenbrock 4 (by decide) (Function.update x j t))
      (x j)

/-! ## Recursive summation and the results of section 2 -/

/-- Exact sum of a finite input vector. -/
noncomputable def p01ExactSum (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i

/-- Absolute input sum used in the paper's forward-error bounds. -/
noncomputable def p01AbsoluteSum (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |v i|

/-- The computed recursive-summation error `E_n = S_hat_n - S_n`. -/
noncomputable def p01RecursiveError
    (flAdd : ℝ → ℝ → ℝ) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  p01RecursiveSum flAdd n v - p01ExactSum n v

/-- The computed sum of the first `k+1` entries, for an explicitly supplied
floating-point addition operation. -/
noncomputable def p01RecursivePrefixWith
    (flAdd : ℝ → ℝ → ℝ) (n : ℕ) (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  p01RecursiveSum flAdd (k.val + 1) fun i =>
    v ⟨i.val, by omega⟩

/-- The computed sum of the first `k+1` entries of `v`. -/
noncomputable def p01RecursivePrefix
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  p01RecursiveSum fp.fl_add (k.val + 1) fun i =>
    v ⟨i.val, by omega⟩

/-- The preceding input index, used only when the supplied index is positive. -/
def p01PreviousIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

/-- The local recurrence assumed when equation (2.2) is expanded. -/
def P01RecursiveDeltaRecurrence
    (flAdd : ℝ → ℝ → ℝ) (n : ℕ) (v : Fin n → ℝ) (δ : Fin n → ℝ) : Prop :=
  (∀ k : Fin n, 0 < k.val →
    p01RecursivePrefixWith flAdd n v k =
      (p01RecursivePrefixWith flAdd n v (p01PreviousIndex k) + v k) *
        (1 + δ k)) ∧
  ∀ h : 0 < n,
    p01RecursivePrefixWith flAdd n v ⟨0, h⟩ = v ⟨0, h⟩

/-- Stepwise rounding witnesses for recursive summation, corresponding to (2.1). -/
def P01RecursiveDeltaWitness
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) (δ : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, 0 < k.val →
    |δ k| ≤ fp.u ∧
    p01RecursivePrefix fp n v k =
      (p01RecursivePrefix fp n v (p01PreviousIndex k) + v k) * (1 + δ k)

/-- Number of rounded additions through which input `i` passes in (2.2). -/
def p01RecursivePathLength (n : ℕ) (i : Fin n) : ℕ :=
  n - max 1 i.val

/-- Product of the rounding factors affecting input `i` in (2.2). -/
noncomputable def p01RecursivePathFactor
    (n : ℕ) (δ : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ k : Fin n, if max 1 i.val ≤ k.val then 1 + δ k else 1

/-- The product expansion on the right side of equation (2.2). -/
noncomputable def p01RecursiveProductExpansion
    (n : ℕ) (v δ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i * p01RecursivePathFactor n δ i

/-- A collection of product remainders used in equations (2.3)--(2.5). -/
def P01RecursiveThetaWitness
    (fp : P01StandardAddModel) (n : ℕ) (v θ : Fin n → ℝ) : Prop :=
  p01RecursiveSum fp.fl_add n v = ∑ i : Fin n, v i * (1 + θ i) ∧
    (∀ i : Fin n, |θ i| ≤ p01Gamma fp.u (p01RecursivePathLength n i)) ∧
    ∀ h : 1 < n, θ ⟨0, by omega⟩ = θ ⟨1, h⟩

/-- The paper's summation condition number `R_n`. -/
noncomputable def p01SummationCondition (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  p01AbsoluteSum n v / |p01ExactSum n v|

/-- Shared qualitative scope used by the heavy-cancellation claims. -/
structure P01HeavyCancellationScopeReport where
  absoluteInputSum : (n : ℕ) → (Fin n → ℝ) → ℝ
  absoluteExactSum : (n : ℕ) → (Fin n → ℝ) → ℝ
  absoluteInputSumReportedMuchLarger : Bool
  quantitativeThresholdSpecified : Bool

noncomputable def p01HeavyCancellationScopeReport :
    P01HeavyCancellationScopeReport :=
  { absoluteInputSum := p01AbsoluteSum
    absoluteExactSum := fun n v => |p01ExactSum n v|
    absoluteInputSumReportedMuchLarger := true
    quantitativeThresholdSpecified := false }

/-- Componentwise relative perturbations used in the condition-number claim. -/
def P01ComponentwisePerturbation
    (n : ℕ) (v dv : Fin n → ℝ) (ε : ℝ) : Prop :=
  ∀ i, |dv i| ≤ ε * |v i|

/-- The sum of computed prefix magnitudes in equations (2.8) and the Psum objective. -/
noncomputable def p01RecursiveRunningMagnitude
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, if 0 < k.val then |p01RecursivePrefix fp n v k| else 0

/-! ## Ordering problems and algorithms -/

/-- Apply a permutation to a finite input vector. -/
def p01Permuted {n : ℕ} (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => v (p i)

/-- Status-preserving form of the paper's general ordering-dependence statement. -/
structure P01DifferentOrderingComputedSumsStatusReport where
  concernsDifferentOrderingsOfTheSameInputTerms : Bool
  arithmeticIsFloatingPoint : Bool
  differentOrderingsReportedInGeneralToYieldDifferentComputedSums : Bool
  meaningOfInGeneralSpecified : Bool

def p01DifferentOrderingComputedSumsStatusReport :
    P01DifferentOrderingComputedSumsStatusReport :=
  { concernsDifferentOrderingsOfTheSameInputTerms := true
    arithmeticIsFloatingPoint := true
    differentOrderingsReportedInGeneralToYieldDifferentComputedSums := true
    meaningOfInGeneralSpecified := false }

/-- Increasing absolute-value order. Ties are deliberately left unspecified. -/
def P01IncreasingMagnitude {n : ℕ}
    (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → |v (p i)| ≤ |v (p j)|

/-- Decreasing absolute-value order. Ties are deliberately left unspecified. -/
def P01DecreasingMagnitude {n : ℕ}
    (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → |v (p j)| ≤ |v (p i)|

/-- The order-dependent right side of equation (2.5). -/
noncomputable def p01Eq25Budget
    (u : ℝ) {n : ℕ} (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n,
    |v (p i)| * p01Gamma u (p01RecursivePathLength n i)

/-- The combinatorial objective suggested by equation (2.8). -/
noncomputable def p01PsumObjective
    (fp : P01StandardAddModel) {n : ℕ} (v : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : ℝ :=
  p01RecursiveRunningMagnitude fp n (p01Permuted v p)

/-- A solution of the global Psum ordering problem. -/
def P01PsumOptimal
    (fp : P01StandardAddModel) {n : ℕ} (v : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ q : Equiv.Perm (Fin n), p01PsumObjective fp v p ≤ p01PsumObjective fp v q

/-- Qualitative status of globally minimizing the equation-(2.8) prefix objective. -/
structure P01PsumGlobalOptimizationCostReport where
  objective :
    (n : ℕ) → P01StandardAddModel → (Fin n → ℝ) → Equiv.Perm (Fin n) → ℝ
  globalMinimizationIsACombinatorialOptimizationProblem : Bool
  reportedTooExpensiveInTheContextOfSummation : Bool

noncomputable def p01PsumGlobalOptimizationCostReport :
    P01PsumGlobalOptimizationCostReport :=
  { objective := fun _ fp v p => p01PsumObjective fp v p
    globalMinimizationIsACombinatorialOptimizationProblem := true
    reportedTooExpensiveInTheContextOfSummation := true }

/-- Whether original index `j` was selected before output position `k`. -/
def P01SelectedBefore {n : ℕ}
    (p : Equiv.Perm (Fin n)) (k j : Fin n) : Prop :=
  ∃ i : Fin n, i.val < k.val ∧ p i = j

/-- Candidate modulus used by the sequential Psum rule. -/
noncomputable def p01PsumCandidate
    (flAdd : ℝ → ℝ → ℝ) {n : ℕ} (v : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) (k j : Fin n) : ℝ :=
  if k.val = 0 then |v j|
  else
    |flAdd
      (p01RecursiveSum flAdd k.val fun i =>
        p01Permuted v p ⟨i.val, lt_trans i.isLt k.isLt⟩)
      (v j)|

/-- The paper's greedy Psum ordering, with nondeterministic tie breaking. -/
def P01PsumOrder
    (flAdd : ℝ → ℝ → ℝ) {n : ℕ} (v : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ k j : Fin n, ¬ P01SelectedBefore p k j →
    p01PsumCandidate flAdd v p k (p k) ≤ p01PsumCandidate flAdd v p k j

/-- Entries occur in nondecreasing order of magnitude. -/
def P01MagnitudeNondecreasing {n : ℕ} (v : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val ≤ j.val → |v i| ≤ |v j|

/-- The implementation-complexity claim made for Psum, whose code is not supplied. -/
structure P01PsumComplexityReport where
  comparisonOrderNLogN : Bool
  implementationReportedToExist : Bool

def p01PsumComplexityReport : P01PsumComplexityReport :=
  { comparisonOrderNLogN := true
    implementationReportedToExist := true }

/-- The source's near-attainability input family; `i=0` is its printed `x(1)`. -/
noncomputable def p01NearAttainabilityInput
    (r t : ℕ) (i : Fin (2 ^ r)) : ℝ :=
  if i.val = 0 then 1
  else 1 - (2 : ℝ) ^ ((Nat.log 2 i.val : ℤ) - (t : ℤ))

/-- The stepwise rounding behavior stated for the near-attainability construction. -/
def P01NearAttainabilityRoundingTrace
    (flAdd : ℝ → ℝ → ℝ) (r t : ℕ) : Prop :=
  ∀ k : Fin (2 ^ r),
    flAdd (k.val : ℝ) (p01NearAttainabilityInput r t k) = k.val + 1

/-- Qualitative parameter regime stated for the near-attainability family. -/
structure P01NearAttainabilityQualitativeRegimeReport where
  equation28Equation25Equation26BoundsReportedNearlyAttainable : Bool
  unitRoundoffSetToTwoToNegativeT : Bool
  inputLengthSetToTwoToR : Bool
  comparedParametersAreRAndT : Bool
  rReportedMuchSmallerThanT : Bool
  quantitativeMeaningSpecified : Bool

def p01NearAttainabilityQualitativeRegimeReport :
    P01NearAttainabilityQualitativeRegimeReport :=
  { equation28Equation25Equation26BoundsReportedNearlyAttainable := true
    unitRoundoffSetToTwoToNegativeT := true
    inputLengthSetToTwoToR := true
    comparedParametersAreRAndT := true
    rReportedMuchSmallerThanT := true
    quantitativeMeaningSpecified := false }

/-- Status of the discarded-bit trace assertion under that qualitative regime. -/
structure P01NearAttainabilityRoundingTraceStatusReport where
  tracePredicate : (ℝ → ℝ → ℝ) → ℕ → ℕ → Prop
  appliesUnderRMuchSmallerThanT : Bool
  sourceAssertsDiscardedBitTrace : Bool
  quantitativeSeparationSpecified : Bool

def p01NearAttainabilityRoundingTraceStatusReport :
    P01NearAttainabilityRoundingTraceStatusReport :=
  { tracePredicate := P01NearAttainabilityRoundingTrace
    appliesUnderRMuchSmallerThanT := true
    sourceAssertsDiscardedBitTrace := true
    quantitativeSeparationSpecified := false }

/-- Equation (2.9)'s four symbolic inputs. -/
def p01Eq29Input (M : ℝ) : Fin 4 → ℝ := ![1, M, 2 * M, -3 * M]

/-- The increasing-magnitude ordering printed in example (2.9). -/
def p01Eq29IncreasingPerm : Equiv.Perm (Fin 4) := Equiv.refl (Fin 4)

/-- The Psum ordering printed in example (2.9). -/
def p01Eq29PsumPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap ⟨2, by omega⟩ ⟨3, by omega⟩

/-- The decreasing-magnitude ordering printed in example (2.9). -/
def p01Eq29DecreasingPerm : Equiv.Perm (Fin 4) :=
  (Equiv.swap ⟨0, by omega⟩ ⟨3, by omega⟩).trans
    (Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩)

/-! ## The general addition class and section 3 -/

/-- A binary addition tree representing a method of the form (3.1). -/
inductive P01SumTree
  | leaf (x : ℝ)
  | node (left right : P01SumTree)

namespace P01SumTree

/-- Leaves, in their tree order. -/
def leaves : P01SumTree → List ℝ
  | .leaf x => [x]
  | .node left right => leaves left ++ leaves right

/-- Number of internal additions traversed by each leaf, in leaf order. -/
def leafDepths : P01SumTree → List ℕ
  | .leaf _ => [0]
  | .node left right =>
      (leafDepths left).map Nat.succ ++ (leafDepths right).map Nat.succ

/-- Exact evaluation of an addition tree. -/
noncomputable def exact : P01SumTree → ℝ
  | .leaf x => x
  | .node left right => exact left + exact right

/-- Rounded evaluation of an addition tree. -/
noncomputable def rounded (flAdd : ℝ → ℝ → ℝ) : P01SumTree → ℝ
  | .leaf x => x
  | .node left right => flAdd (rounded flAdd left) (rounded flAdd right)

/-- Local errors, one for each internal addition. -/
noncomputable def localErrors (flAdd : ℝ → ℝ → ℝ) : P01SumTree → List ℝ
  | .leaf _ => []
  | .node left right =>
      localErrors flAdd left ++ localErrors flAdd right ++
        [flAdd (rounded flAdd left) (rounded flAdd right) -
          (rounded flAdd left + rounded flAdd right)]

/-- Rounded internal-node values `T_hat_k`. -/
noncomputable def internalValues (flAdd : ℝ → ℝ → ℝ) : P01SumTree → List ℝ
  | .leaf _ => []
  | .node left right =>
      internalValues flAdd left ++ internalValues flAdd right ++
        [rounded flAdd (.node left right)]

/-- Exact values at every leaf and internal node of an addition tree. -/
noncomputable def exactValues : P01SumTree → List ℝ
  | .leaf x => [x]
  | .node left right =>
      exactValues left ++ exactValues right ++ [exact (.node left right)]

end P01SumTree

/-- A tree representation used internally by the paper's tree-based results. -/
def P01TreeAdditionScheme (xs : List ℝ) (tree : P01SumTree) : Prop :=
  tree.leaves.Perm xs ∧
    (P01SumTree.internalValues (· + ·) tree).length = xs.length - 1

/-- The literal one-based indexed computation printed in equation (3.1). -/
def P01Equation31Trace
    (n : ℕ) (x : Fin n → ℝ) (T : ℕ → ℝ) (S : ℝ) : Prop :=
  0 < n ∧
  (∀ k : Fin n, T (k.val + 1) = x k) ∧
  (∀ k : ℕ, n + 1 ≤ k → k ≤ 2 * n - 1 →
    ∃ k₁ k₂ : ℕ,
      1 ≤ k₁ ∧ k₁ < k₂ ∧ k₂ < k ∧
      T k = T k₁ + T k₂) ∧
  S = T (2 * n - 1)

/-- Equation (3.1): a general addition scheme is exactly a literal indexed
trace beginning with the supplied inputs and returning its last entry. -/
def P01AdditionScheme
    (n : ℕ) (x : Fin n → ℝ) (S : ℝ) : Prop :=
  ∃ T : ℕ → ℝ, P01Equation31Trace n x T S

/-- Every internal addition has at least one original input as an operand. -/
def P01EveryAdditionHasOriginalOperand : P01SumTree → Prop
  | .leaf _ => True
  | .node (.leaf _) right => P01EveryAdditionHasOriginalOperand right
  | .node left (.leaf _) => P01EveryAdditionHasOriginalOperand left
  | .node (.node _ _) (.node _ _) => False

/-- Equation (3.2), expressed simultaneously at all internal nodes. -/
def P01TreeRespectsStandardModel
    (fp : P01StandardAddModel) : P01SumTree → Prop
  | .leaf _ => True
  | .node left right =>
      (∃ δ : ℝ,
        |δ| ≤ fp.u ∧
        P01SumTree.rounded fp.fl_add (.node left right) =
          (P01SumTree.rounded fp.fl_add left +
            P01SumTree.rounded fp.fl_add right) * (1 + δ)) ∧
      P01TreeRespectsStandardModel fp left ∧
      P01TreeRespectsStandardModel fp right

/-- Sum of the magnitudes of all computed internal nodes. -/
noncomputable def p01TreeRunningMagnitude
    (flAdd : ℝ → ℝ → ℝ) (tree : P01SumTree) : ℝ :=
  (P01SumTree.internalValues flAdd tree).map abs |>.sum

/-- The reported experiment metric `T`, including its printed internal-node
indexing convention and the compensated-method exclusion. -/
structure P01ReportedRunningMagnitudeTReport where
  value : ℝ
  indicatesSharpnessOfErrorBounds : Bool
  sumsComputedIntermediateValuesIndexedFromNPlusOneThroughTwoNMinusOne : Bool
  reportedForEveryMethodExceptCompensatedSummation : Bool

noncomputable def p01ReportedRunningMagnitudeT
    (flAdd : ℝ → ℝ → ℝ) (tree : P01SumTree) :
    P01ReportedRunningMagnitudeTReport :=
  { value := p01TreeRunningMagnitude flAdd tree
    indicatesSharpnessOfErrorBounds := true
    sumsComputedIntermediateValuesIndexedFromNPlusOneThroughTwoNMinusOne := true
    reportedForEveryMethodExceptCompensatedSummation := true }

/-! ### Pairwise summation -/

/-- One adjacent-pair stage, carrying an odd last term unchanged. -/
inductive P01PairwiseStage (flAdd : ℝ → ℝ → ℝ) : List ℝ → List ℝ → Prop
  | nil : P01PairwiseStage flAdd [] []
  | carry (x : ℝ) : P01PairwiseStage flAdd [x] [x]
  | pair (x y : ℝ) {xs ys : List ℝ}
      (rest : P01PairwiseStage flAdd xs ys) :
      P01PairwiseStage flAdd (x :: y :: xs) (flAdd x y :: ys)

/-- Repeated pairwise stages until zero or one value remains. -/
inductive P01PairwiseEvaluation (flAdd : ℝ → ℝ → ℝ) : List ℝ → ℝ → Prop
  | empty : P01PairwiseEvaluation flAdd [] 0
  | singleton (x : ℝ) : P01PairwiseEvaluation flAdd [x] x
  | step {x y : ℝ} {xs next : List ℝ} {s : ℝ}
      (stage : P01PairwiseStage flAdd (x :: y :: xs) next)
      (tail : P01PairwiseEvaluation flAdd next s) :
      P01PairwiseEvaluation flAdd (x :: y :: xs) s

/-- One structural adjacent-pair stage, carrying an odd final tree unchanged. -/
inductive P01PairwiseTreeStage : List P01SumTree → List P01SumTree → Prop
  | nil : P01PairwiseTreeStage [] []
  | carry (tree : P01SumTree) : P01PairwiseTreeStage [tree] [tree]
  | pair (left right : P01SumTree) {trees next : List P01SumTree}
      (rest : P01PairwiseTreeStage trees next) :
      P01PairwiseTreeStage (left :: right :: trees) (.node left right :: next)

/-- Repeated structural pairwise stages until a single addition tree remains. -/
inductive P01PairwiseTreeReduction : List P01SumTree → P01SumTree → Prop
  | singleton (tree : P01SumTree) : P01PairwiseTreeReduction [tree] tree
  | step {left right : P01SumTree} {trees next : List P01SumTree}
      {result : P01SumTree}
      (stage : P01PairwiseTreeStage (left :: right :: trees) next)
      (tail : P01PairwiseTreeReduction next result) :
      P01PairwiseTreeReduction (left :: right :: trees) result

/-- The pairwise parenthesization obtained from the source inputs. -/
def P01PairwiseTreeEvaluation (inputs : List ℝ) (tree : P01SumTree) : Prop :=
  P01PairwiseTreeReduction (inputs.map P01SumTree.leaf) tree

/-- Pairwise evaluation with its number of parallel stages exposed. -/
inductive P01PairwiseEvaluationStages (flAdd : ℝ → ℝ → ℝ) :
    List ℝ → ℕ → ℝ → Prop
  | empty : P01PairwiseEvaluationStages flAdd [] 0 0
  | singleton (x : ℝ) : P01PairwiseEvaluationStages flAdd [x] 0 x
  | step {x y : ℝ} {xs next : List ℝ} {stages : ℕ} {s : ℝ}
      (stage : P01PairwiseStage flAdd (x :: y :: xs) next)
      (tail : P01PairwiseEvaluationStages flAdd next stages s) :
      P01PairwiseEvaluationStages flAdd (x :: y :: xs) (stages + 1) s

/-- The ceiling of `log₂ n`, expressed without a real logarithm. -/
def p01CeilLog2 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log 2 (n - 1) + 1

/-- Finite and infinite inverse-power sums used for the coefficients in (3.7). -/
noncomputable def p01InversePowerPartial (power n : ℕ) : ℝ :=
  ∑ i : Fin n, 1 / ((i.val + 1 : ℕ) : ℝ) ^ power

noncomputable def p01InversePowerSeries (power : ℕ) : ℝ :=
  ∑' i : ℕ, 1 / ((i + 1 : ℕ) : ℝ) ^ power

/-- Status-aware record for the source's decimal inverse-power coefficients.
The paper uses `≈` without specifying an approximation tolerance. -/
structure P01InversePowerCoefficientApproximationReport where
  power : ℕ
  finitePartialCoefficient : ℕ → ℝ
  infiniteSeriesCoefficient : ℝ
  finitePartialReportedApproximatelyInfinite : Bool
  reportedDecimalCoefficient : ℚ
  approximationToleranceSpecified : Bool

noncomputable def p01InverseCubeCoefficientApproximationReport :
    P01InversePowerCoefficientApproximationReport :=
  { power := 3
    finitePartialCoefficient := p01InversePowerPartial 3
    infiniteSeriesCoefficient := p01InversePowerSeries 3
    finitePartialReportedApproximatelyInfinite := true
    reportedDecimalCoefficient := 6 / 5
    approximationToleranceSpecified := false }

noncomputable def p01InverseSquareCoefficientApproximationReport :
    P01InversePowerCoefficientApproximationReport :=
  { power := 2
    finitePartialCoefficient := p01InversePowerPartial 2
    infiniteSeriesCoefficient := p01InversePowerSeries 2
    finitePartialReportedApproximatelyInfinite := true
    reportedDecimalCoefficient := 41 / 25
    approximationToleranceSpecified := false }

/-- Status of the source's approximate inverse-cube comparison.  The printed
`≈ log₂ n` relation is qualitative because no tolerance is supplied. -/
structure P01InverseCubeApproximateLogComparisonReport where
  inputTermsAreReciprocalCubes : Bool
  comparedPairwiseEquation37Bound : Bool
  comparedIncreasingRecursiveEquation25Bound : Bool
  comparisonIsMultiplicative : Bool
  comparisonFactorIsLogTwoOfInputLength : Bool
  pairwiseBoundReportedApproximatelyLogTwoLarger : Bool
  approximationToleranceSpecified : Bool

def p01InverseCubeApproximateLogComparisonReport :
    P01InverseCubeApproximateLogComparisonReport :=
  { inputTermsAreReciprocalCubes := true
    comparedPairwiseEquation37Bound := true
    comparedIncreasingRecursiveEquation25Bound := true
    comparisonIsMultiplicative := true
    comparisonFactorIsLogTwoOfInputLength := true
    pairwiseBoundReportedApproximatelyLogTwoLarger := true
    approximationToleranceSpecified := false }

/-- Recursive evaluation on a list, keeping its first input exact. -/
noncomputable def p01RecursiveList
    (flAdd : ℝ → ℝ → ℝ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => xs.foldl flAdd x

/-- The left-deep addition tree underlying ordinary recursive summation. -/
def p01RecursiveTree : List ℝ → Option P01SumTree
  | [] => none
  | x :: xs => some (xs.foldl (fun tree y => .node tree (.leaf y)) (.leaf x))

/-- Status-preserving form of the disputed nonrecursive-method clause after
(3.1).  The paper's later insertion trace supplies the consistency check. -/
structure P01OtherGeneralMethodsStructuralSourceErrorReport where
  otherThreeReportedToContainAComputedComputedAddition : Bool
  literalUniversalClauseConsistentWithLaterInsertionExample : Bool

def p01OtherGeneralMethodsStructuralSourceErrorReport :
    P01OtherGeneralMethodsStructuralSourceErrorReport :=
  { otherThreeReportedToContainAComputedComputedAddition := true
    literalUniversalClauseConsistentWithLaterInsertionExample := false }

/-! ### Insertion and sign-separated summation -/

/-- A list is ordered by nondecreasing absolute value. -/
def P01AbsNondecreasing (xs : List ℝ) : Prop :=
  xs.Pairwise fun x y => |x| ≤ |y|

/-- One insertion-summation step: add the first two values and reinsert their sum. -/
def P01InsertionStep
    (flAdd : ℝ → ℝ → ℝ) (xs ys : List ℝ) : Prop :=
  ∃ a b : ℝ, ∃ rest : List ℝ,
    xs = a :: b :: rest ∧
    ys.Perm (flAdd a b :: rest) ∧
    P01AbsNondecreasing ys

/-- The insertion algorithm, including its initial magnitude sort and unspecified ties. -/
def P01InsertionEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ ordered : List ℝ,
    ordered.Perm inputs ∧ P01AbsNondecreasing ordered ∧
    Relation.ReflTransGen (P01InsertionStep flAdd) ordered [result]

/-- A specialized insertion step whose merged value remains at the front. -/
def P01InsertionFrontStep
    (flAdd : ℝ → ℝ → ℝ) (xs ys : List ℝ) : Prop :=
  ∃ a b : ℝ, ∃ rest : List ℝ,
    xs = a :: b :: rest ∧ ys = flAdd a b :: rest ∧
    P01AbsNondecreasing ys

/-- An insertion run in which every merged value is reinserted at the front. -/
def P01InsertionFrontEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ ordered : List ℝ,
    ordered.Perm inputs ∧ P01AbsNondecreasing ordered ∧
    Relation.ReflTransGen (P01InsertionFrontStep flAdd) ordered [result]

/-- A specialized insertion step whose merged value is appended at the end. -/
def P01InsertionBackStep
    (flAdd : ℝ → ℝ → ℝ) (xs ys : List ℝ) : Prop :=
  ∃ a b : ℝ, ∃ rest : List ℝ,
    xs = a :: b :: rest ∧ ys = rest ++ [flAdd a b] ∧
    P01AbsNondecreasing ys

/-- An insertion run in which every merged value is reinserted at the end. -/
def P01InsertionBackEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ ordered : List ℝ,
    ordered.Perm inputs ∧ P01AbsNondecreasing ordered ∧
    Relation.ReflTransGen (P01InsertionBackStep flAdd) ordered [result]

/-- The paper's literal computed-(3.4) insertion-optimality assertion.
It is retained as an attributed claim because it is false for some permitted
round-to-nearest binary inputs. -/
structure P01InsertionOptimalityReport where
  assertedForAllPositiveInputs : Bool
  concernsTermsInErrorExpression33 : Bool
  comparisonClassIsAllMethodsOfFormEquation31 : Bool
  minimizesEquation34AmongAdditionTrees : Bool

def p01InsertionOptimalityReport : P01InsertionOptimalityReport :=
  { assertedForAllPositiveInputs := true
    concernsTermsInErrorExpression33 := true
    comparisonClassIsAllMethodsOfFormEquation31 := true
    minimizesEquation34AmongAdditionTrees := true }

/-- The geometric family underlying the printed power-of-two insertion trace. -/
noncomputable def p01PowersOfTwo (n : ℕ) : List ℝ :=
  (List.range n).map fun k => (2 : ℝ) ^ k

/-- The source-order negative subsequence for sign-separated summation. -/
noncomputable def p01PlusMinusNegativeInputs (inputs : List ℝ) : List ℝ :=
  inputs.filter fun x => x < 0

/-- The source-order nonnegative subsequence for sign-separated summation.
Zeros are assigned to this side so every original input remains a leaf. -/
noncomputable def p01PlusMinusNonnegativeInputs (inputs : List ℝ) : List ℝ :=
  inputs.filter fun x => 0 ≤ x

/-- The explicitly named final floating-point combination `S₊ + S₋`. -/
noncomputable def p01PlusMinusConceptualFinal
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) : ℝ :=
  flAdd
    (p01RecursiveList flAdd (p01PlusMinusNonnegativeInputs inputs))
    (p01RecursiveList flAdd (p01PlusMinusNegativeInputs inputs))

/-- The sign-separated equation-(3.1) tree.  Each sign subtotal is accumulated
recursively in its order from the input list.  When both sign classes occur,
the root is the final `S₊ + S₋` addition.  For an empty sign class, the
redundant zero-side operation is elided so the tree has exactly the original
inputs as leaves and exactly `n - 1` additions. -/
noncomputable def P01PlusMinusTree
    (_flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (tree : P01SumTree) : Prop :=
  let negatives := p01PlusMinusNegativeInputs inputs
  let nonnegatives := p01PlusMinusNonnegativeInputs inputs
  (negatives = [] ∧ p01RecursiveTree nonnegatives = some tree) ∨
  (nonnegatives = [] ∧ p01RecursiveTree negatives = some tree) ∨
  ∃ negativeTree nonnegativeTree : P01SumTree,
    p01RecursiveTree negatives = some negativeTree ∧
    p01RecursiveTree nonnegatives = some nonnegativeTree ∧
    tree = .node nonnegativeTree negativeTree

/-- The equation-(3.1) operational value of sign-separated summation.  It is
the explicit final combination when both subtotals exist and elides only a
redundant addition with an empty subtotal otherwise. -/
noncomputable def p01PlusMinusFinal
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) : ℝ :=
  let negatives := p01PlusMinusNegativeInputs inputs
  let nonnegatives := p01PlusMinusNonnegativeInputs inputs
  if negatives = [] then p01RecursiveList flAdd nonnegatives
  else if nonnegatives = [] then p01RecursiveList flAdd negatives
  else p01PlusMinusConceptualFinal flAdd inputs

/-- One of the methods available before the paper introduces plus/minus
summation: recursive summation in a chosen order, pairwise summation, or
insertion summation. -/
def P01PreviouslySpecifiedSubtotalEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  (∃ ordered : List ℝ,
      ordered.Perm inputs ∧ result = p01RecursiveList flAdd ordered) ∨
  P01PairwiseEvaluation flAdd inputs result ∨
  P01InsertionEvaluation flAdd inputs result

/-- Sign-separated summation.  Each nonempty sign subtotal may be evaluated
by any method specified earlier in the paper; when both sign classes occur,
their two results are joined by the final floating-point addition. -/
def P01PlusMinusEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  let negatives := p01PlusMinusNegativeInputs inputs
  let nonnegatives := p01PlusMinusNonnegativeInputs inputs
  (negatives = [] ∧
      P01PreviouslySpecifiedSubtotalEvaluation flAdd nonnegatives result) ∨
  (nonnegatives = [] ∧
      P01PreviouslySpecifiedSubtotalEvaluation flAdd negatives result) ∨
  (∃ negativeResult nonnegativeResult : ℝ,
      negatives ≠ [] ∧ nonnegatives ≠ [] ∧
      P01PreviouslySpecifiedSubtotalEvaluation flAdd negatives negativeResult ∧
      P01PreviouslySpecifiedSubtotalEvaluation flAdd nonnegatives nonnegativeResult ∧
      result = flAdd nonnegativeResult negativeResult)

/-- The alternating integer family used to expose the large sign-separated intermediates. -/
def p01AlternatingIntegers (m : ℕ) : List ℝ :=
  (List.range m).flatMap fun k => [-(k + 1 : ℝ), (k + 1 : ℝ)]

/-- The same alternating family as a finite vector. -/
def p01AlternatingVector (m : ℕ) (i : Fin (2 * m)) : ℝ :=
  if i.val % 2 = 0 then -((i.val / 2 + 1 : ℕ) : ℝ)
  else ((i.val / 2 + 1 : ℕ) : ℝ)

/-! ### Error-free correction and compensated summation -/

/-- Unbounded-exponent, precision-`p`, radix-two floating-point numbers. -/
def P01BaseTwoRepresentable (p : ℕ) (x : ℝ) : Prop :=
  x = 0 ∨ ∃ m e : ℤ,
    m.natAbs < 2 ^ p ∧ x = (m : ℝ) * (2 : ℝ) ^ e

/-- The two round-to-nearest tie conventions allowed in the footnote to (2.9). -/
inductive P01NearestTiePolicy
  | evenLastDigit
  | awayFromZero

/-- A normalized binary significand has an even least significant bit. -/
def P01BaseTwoEvenLastBit (precision : ℕ) (x : ℝ) : Prop :=
  x = 0 ∨ ∃ m e : ℤ,
    2 ^ (precision - 1) ≤ m.natAbs ∧ m.natAbs < 2 ^ precision ∧
    Even m ∧ x = (m : ℝ) * (2 : ℝ) ^ e

/-- Semantic form of the two permitted nearest-tie conventions. -/
def P01PermittedBinaryTieRule
    (precision : ℕ) (policy : P01NearestTiePolicy) (round : ℝ → ℝ) : Prop :=
  match policy with
  | .awayFromZero =>
      ∀ x y, P01BaseTwoRepresentable precision y →
        |x - round x| = |x - y| → |y| ≤ |round x|
  | .evenLastDigit =>
      ∀ x y, P01BaseTwoRepresentable precision y →
        |x - round x| = |x - y| →
        P01BaseTwoEvenLastBit precision y → round x = y

/-- Unbounded-exponent, precision-`p` numbers in an arbitrary machine radix. -/
def P01BaseRepresentable (radix precision : ℕ) (x : ℝ) : Prop :=
  x = 0 ∨ ∃ m e : ℤ,
    m.natAbs < radix ^ precision ∧ x = (m : ℝ) * (radix : ℝ) ^ e

/-- A normalized radix-`β` significand has an even least significant digit. -/
def P01BaseEvenLastDigit (radix precision : ℕ) (x : ℝ) : Prop :=
  x = 0 ∨ ∃ m e : ℤ,
    radix ^ (precision - 1) ≤ m.natAbs ∧ m.natAbs < radix ^ precision ∧
    Even (m.natAbs % radix) ∧ x = (m : ℝ) * (radix : ℝ) ^ e

/-- Semantic tie rule for the radix model in the example's footnote. -/
def P01PermittedRadixTieRule
    (radix precision : ℕ) (policy : P01NearestTiePolicy)
    (round : ℝ → ℝ) : Prop :=
  match policy with
  | .awayFromZero =>
      ∀ x y, P01BaseRepresentable radix precision y →
        |x - round x| = |x - y| → |y| ≤ |round x|
  | .evenLastDigit =>
      ∀ x y, P01BaseRepresentable radix precision y →
        |x - round x| = |x - y| →
        P01BaseEvenLastDigit radix precision y → round x = y

/-- A round-to-nearest model in the machine radix used by example (2.9). -/
structure P01RadixRoundModel where
  radix : ℕ
  radix_ge_two : 2 ≤ radix
  precision : ℕ
  precision_pos : 0 < precision
  tiePolicy : P01NearestTiePolicy
  round : ℝ → ℝ
  round_mem : ∀ x, P01BaseRepresentable radix precision (round x)
  round_exact : ∀ x, P01BaseRepresentable radix precision x → round x = x
  nearest : ∀ x y, P01BaseRepresentable radix precision y →
    |x - round x| ≤ |x - y|
  neg_round : ∀ x, round (-x) = -round x
  tie_rule : P01PermittedRadixTieRule radix precision tiePolicy round

/-- Unit roundoff of the unbounded radix/precision model. -/
noncomputable def p01RadixUnitRoundoff (fp : P01RadixRoundModel) : ℝ :=
  (1 / 2 : ℝ) * (fp.radix : ℝ) ^ (1 - (fp.precision : ℤ))

/-- Rounded addition in the radix model used by (2.9). -/
noncomputable def p01RadixRoundAdd
    (fp : P01RadixRoundModel) (x y : ℝ) : ℝ :=
  fp.round (x + y)

/-- A deterministic round-to-nearest operation on a binary format. -/
structure P01BinaryRoundModel where
  precision : ℕ
  precision_pos : 0 < precision
  tiePolicy : P01NearestTiePolicy
  round : ℝ → ℝ
  round_mem : ∀ x, P01BaseTwoRepresentable precision (round x)
  round_exact : ∀ x, P01BaseTwoRepresentable precision x → round x = x
  nearest : ∀ x y, P01BaseTwoRepresentable precision y →
    |x - round x| ≤ |x - y|
  neg_round : ∀ x, round (-x) = -round x
  tie_rule : P01PermittedBinaryTieRule precision tiePolicy round

/-- Binary round-to-nearest addition induced by the unary rounding operation. -/
noncomputable def p01RoundAdd (fp : P01BinaryRoundModel) (x y : ℝ) : ℝ :=
  fp.round (x + y)

/-- Unit roundoff of the binary precision model. -/
noncomputable def p01BinaryUnitRoundoff (fp : P01BinaryRoundModel) : ℝ :=
  (2 : ℝ) ^ (-(fp.precision : ℤ))

/-- The computed sum in the correction construction preceding (3.9). -/
noncomputable def p01FastTwoSum (fp : P01BinaryRoundModel) (a b : ℝ) : ℝ :=
  p01RoundAdd fp a b

/-- Kahan's computed correction, evaluated in the printed parenthesization. -/
noncomputable def p01FastTwoSumCorrection
    (fp : P01BinaryRoundModel) (a b : ℝ) : ℝ :=
  let s := p01FastTwoSum fp a b
  (-fp.round (fp.round (s - a) - b))

/-- Kahan's two-term rounded sum in an arbitrary machine radix. -/
noncomputable def p01RadixFastTwoSum
    (fp : P01RadixRoundModel) (a b : ℝ) : ℝ :=
  p01RadixRoundAdd fp a b

/-- Kahan's printed correction in an arbitrary machine radix. -/
noncomputable def p01RadixFastTwoSumCorrection
    (fp : P01RadixRoundModel) (a b : ℝ) : ℝ :=
  let s := p01RadixFastTwoSum fp a b
  (-fp.round (fp.round (s - a) - b))

/-- State `(s,e)` of the compensated summation pseudocode. -/
structure P01CompensatedState where
  sum : ℝ
  correction : ℝ

/-- One iteration of the compensated summation algorithm on printed page 791. -/
noncomputable def p01CompensatedStep
    (flAdd : ℝ → ℝ → ℝ) (state : P01CompensatedState) (x : ℝ) :
    P01CompensatedState :=
  let temp := state.sum
  let y := flAdd x state.correction
  let s := flAdd temp y
  let e := flAdd (flAdd temp (-s)) y
  ⟨s, e⟩

/-- Failure of the magnitude premise needed for an exact local correction. -/
structure P01CompensatedCorrectionMagnitudeCaveatReport where
  compensatedMethodReportedToHaveTwoWeaknesses : Bool
  thisIsTheFirstReportedWeakness : Bool
  concernsCorrectionIdentityEquation39 : Bool
  exactnessRequiresFirstAddendMagnitudeAtLeastSecond : Bool
  requiredMagnitudePremiseGuaranteedAtEveryCompensatedStep : Bool
  localCorrectionNecessarilyExact : Bool
  secondReportedWeaknessIsInexactInputCorrectionAddition : Bool

def p01CompensatedCorrectionMagnitudeCaveatReport :
    P01CompensatedCorrectionMagnitudeCaveatReport :=
  { compensatedMethodReportedToHaveTwoWeaknesses := true
    thisIsTheFirstReportedWeakness := true
    concernsCorrectionIdentityEquation39 := true
    exactnessRequiresFirstAddendMagnitudeAtLeastSecond := true
    requiredMagnitudePremiseGuaranteedAtEveryCompensatedStep := false
    localCorrectionNecessarilyExact := false
    secondReportedWeaknessIsInexactInputCorrectionAddition := true }

/-- The separate rounding caveat for forming the corrected next input. -/
structure P01CompensatedInputCorrectionAdditionCaveatReport where
  concernsAdditionOfInputAndPreviousCorrection : Bool
  assignmentIsTheCompensatedStepYValue : Bool
  additionPerformedExactly : Bool

def p01CompensatedInputCorrectionAdditionCaveatReport :
    P01CompensatedInputCorrectionAdditionCaveatReport :=
  { concernsAdditionOfInputAndPreviousCorrection := true
    assignmentIsTheCompensatedStepYValue := true
    additionPerformedExactly := false }

/-- The separately stated relative-accuracy caveat under heavy cancellation. -/
structure P01CompensatedHeavyCancellationCaveatReport where
  scope : P01HeavyCancellationScopeReport
  smallRelativeErrorUnderHeavyCancellationGuaranteed : Bool

noncomputable def p01CompensatedHeavyCancellationCaveatReport :
    P01CompensatedHeavyCancellationCaveatReport :=
  { scope := p01HeavyCancellationScopeReport
    smallRelativeErrorUnderHeavyCancellationGuaranteed := false }

/-- State after processing a finite list by compensated summation. -/
noncomputable def p01CompensatedStateAfter
    (flAdd : ℝ → ℝ → ℝ) (xs : List ℝ) : P01CompensatedState :=
  xs.foldl (p01CompensatedStep flAdd) ⟨0, 0⟩

/-- The sum returned by Kahan's compensated algorithm. -/
noncomputable def p01CompensatedSum
    (flAdd : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  (p01CompensatedStateAfter flAdd xs).sum

/-- Kahan's final-corrected variation, appending `s := s + e`. -/
noncomputable def p01FinalCorrectedSum
    (flAdd : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  let state := p01CompensatedStateAfter flAdd xs
  flAdd state.sum state.correction

/-- A family of standard models whose parameter is exactly the unit roundoff. -/
structure P01StandardAddFamily where
  model : NNReal → P01StandardAddModel
  roundoff_eq : ∀ u : NNReal, (model u).u = (u : ℝ)

/-- The input entries are floating-point data, hence adding a zero correction preserves them. -/
def P01InputsRepresentableForAdd
    (fp : P01StandardAddModel) (n : ℕ) (v : Fin n → ℝ) : Prop :=
  ∀ i, fp.fl_add (v i) 0 = v i

/-- The exact attributed backward representation (3.10), with
O(n*u^2) given its standard one-sided, fixed-problem meaning as u tends to zero. -/
def P01Equation310BackwardRepresentationClaim
    (family : P01StandardAddFamily) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ),
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, 0 < (u : ℝ) → (u : ℝ) ≤ ε →
        P01InputsRepresentableForAdd (family.model u) n v →
        ∃ μ : Fin n → ℝ,
          p01CompensatedSum (family.model u).fl_add (List.ofFn v) =
              ∑ i : Fin n, (1 + μ i) * v i ∧
            ∀ i, |μ i| ≤
              2 * (u : ℝ) + C * (n : ℝ) * (u : ℝ) ^ 2

/-- The exact attributed final-corrected backward representation, whose
quadratic remainder at input i scales with the remaining-input count. -/
def P01FinalCorrectedBackwardRepresentationClaim
    (family : P01StandardAddFamily) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ),
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, 0 < (u : ℝ) → (u : ℝ) ≤ ε →
        P01InputsRepresentableForAdd (family.model u) n v →
        ∃ μ : Fin n → ℝ,
          p01FinalCorrectedSum (family.model u).fl_add (List.ofFn v) =
              ∑ i : Fin n, (1 + μ i) * v i ∧
            ∀ i, |μ i| ≤
              2 * (u : ℝ) +
                C * ((n - i.val : ℕ) : ℝ) * (u : ℝ) ^ 2

/-- The exact attributed forward-error bound (3.11), again interpreting
O(n*u^2) one-sidedly for each fixed input problem. -/
def P01Equation311ForwardErrorClaim
    (family : P01StandardAddFamily) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ),
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
      ∀ u : NNReal, 0 < (u : ℝ) → (u : ℝ) ≤ ε →
        P01InputsRepresentableForAdd (family.model u) n v →
        |p01CompensatedSum (family.model u).fl_add (List.ofFn v) -
            p01ExactSum n v| ≤
          (2 * (u : ℝ) + C * (n : ℝ) * (u : ℝ) ^ 2) *
            p01AbsoluteSum n v

/-- The separate source assertion that one constant works independently of
n throughout the regime n*u <= 1 in (3.11). -/
def P01Equation311NIndependentConstantClaim
    (family : P01StandardAddFamily) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : NNReal, 0 < (u : ℝ) →
      ∀ (n : ℕ) (v : Fin n → ℝ),
        (n : ℝ) * (u : ℝ) ≤ 1 →
        P01InputsRepresentableForAdd (family.model u) n v →
        |p01CompensatedSum (family.model u).fl_add (List.ofFn v) -
            p01ExactSum n v| ≤
          (2 * (u : ℝ) + C * (n : ℝ) * (u : ℝ) ^ 2) *
            p01AbsoluteSum n v

/-- Source-facing attributed form of equation (3.10). It carries the exact
mathematical claim without asserting that the bare model proves it. -/
structure P01Equation310SourceReport where
  claimedRelation : P01StandardAddFamily → Prop
  claimedRelation_eq :
    claimedRelation = P01Equation310BackwardRepresentationClaim
  sourceAssertsClaimedRelation : Bool

/-- Source-facing attributed form of the stronger final-corrected bound. -/
structure P01FinalCorrectedSourceReport where
  claimedRelation : P01StandardAddFamily → Prop
  claimedRelation_eq :
    claimedRelation = P01FinalCorrectedBackwardRepresentationClaim
  sourceAssertsClaimedRelation : Bool

/-- Source-facing attributed form of forward-error bound (3.11). -/
structure P01Equation311SourceReport where
  claimedRelation : P01StandardAddFamily → Prop
  claimedRelation_eq : claimedRelation = P01Equation311ForwardErrorClaim
  sourceAssertsClaimedRelation : Bool

/-- Source-facing attributed form of the n-independent-constant clause. -/
structure P01Equation311NIndependentConstantSourceReport where
  claimedRelation : P01StandardAddFamily → Prop
  claimedRelation_eq :
    claimedRelation = P01Equation311NIndependentConstantClaim
  sourceAssertsClaimedRelation : Bool

def p01_t4_eq_3_10 : P01Equation310SourceReport :=
  { claimedRelation := P01Equation310BackwardRepresentationClaim
    claimedRelation_eq := rfl
    sourceAssertsClaimedRelation := true }

def p01_t4_final_corrected_backward_error :
    P01FinalCorrectedSourceReport :=
  { claimedRelation := P01FinalCorrectedBackwardRepresentationClaim
    claimedRelation_eq := rfl
    sourceAssertsClaimedRelation := true }

def p01_t4_eq_3_11 : P01Equation311SourceReport :=
  { claimedRelation := P01Equation311ForwardErrorClaim
    claimedRelation_eq := rfl
    sourceAssertsClaimedRelation := true }

def p01_t4_compensated_constant_independent_of_n :
    P01Equation311NIndependentConstantSourceReport :=
  { claimedRelation := P01Equation311NIndependentConstantClaim
    claimedRelation_eq := rfl
    sourceAssertsClaimedRelation := true }

/-- Source-facing form of the section-6 first-order compensated-error cap. -/
structure P01CompensatedFirstOrderCapReport where
  sourceAssertsNormalizedErrorFirstOrderCap : Bool
  firstOrderCap : ℕ

/-- The reported first-order normalized-error cap for compensated summation. -/
def p01_t4_first_order_R_cap_compensated :
    P01CompensatedFirstOrderCapReport :=
  { sourceAssertsNormalizedErrorFirstOrderCap := true
    firstOrderCap := 2 }

/-- Status-preserving record of the one-signed accuracy assertion in conclusion item 2.

The paper does not define “perfect relative accuracy” quantitatively, and interpreting it as
relative error at most one unit roundoff is false for inputs allowed by its own round-to-nearest
model.  This is therefore source-report data, not an impossible proof target.
-/
structure P01CompensatedOneSignedAccuracyReport where
  appliesToOneSignedInputs : Bool
  requiresNUnitRoundoffAtMostOne : Bool
  claimedPerfectRelativeAccuracy : Bool

def p01CompensatedOneSignedAccuracyReport : P01CompensatedOneSignedAccuracyReport :=
  { appliesToOneSignedInputs := true
    requiresNUnitRoundoffAtMostOne := true
    claimedPerfectRelativeAccuracy := true }

/-- State for the variant that accumulates, rather than immediately feeds back, corrections. -/
structure P01GlobalCorrectionState where
  sum : ℝ
  correctionSum : ℝ

/-- One step of the accumulated-corrections variation. -/
noncomputable def p01GlobalCorrectionStep
    (flAdd : ℝ → ℝ → ℝ) (state : P01GlobalCorrectionState) (x : ℝ) :
    P01GlobalCorrectionState :=
  let temp := state.sum
  let s := flAdd temp x
  let correction := flAdd (flAdd temp (-s)) x
  ⟨s, flAdd state.correctionSum correction⟩

/-- Accumulate local corrections recursively and add the global correction at the end. -/
noncomputable def p01GlobalCorrectedSum
    (flAdd : ℝ → ℝ → ℝ) (xs : List ℝ) : ℝ :=
  let state := xs.foldl (p01GlobalCorrectionStep flAdd) ⟨0, 0⟩
  flAdd state.sum state.correctionSum

/-! ### Accumulator and distillation specifications -/

/-- Machine-dependent interval accumulators in the Wolfe--Malcolm family. -/
structure P01AccumulatorSystem where
  levelCount : ℕ
  levelCount_pos : 0 < levelCount
  lower : Fin levelCount → ℝ
  upper : Fin levelCount → ℝ
  interval_nonempty : ∀ level, lower level < upper level
  intervals_distinct : Function.Injective (fun level => (lower level, upper level))
  flAdd : ℝ → ℝ → ℝ

/-- Whether a partial sum remains in its level's designated interval. -/
def P01AccumulatorFits
    (sys : P01AccumulatorSystem) (level : Fin sys.levelCount) (value : ℝ) : Prop :=
  sys.lower level ≤ value ∧ value < sys.upper level

/-- One cascade: add at a level, or reset and carry to the next level on overflow. -/
inductive P01AccumulatorCascade
    (sys : P01AccumulatorSystem) :
    Fin sys.levelCount → (Fin sys.levelCount → ℝ) → ℝ →
      (Fin sys.levelCount → ℝ) → Prop
  | stop (level state x)
      (hfit : P01AccumulatorFits sys level (sys.flAdd (state level) x)) :
      P01AccumulatorCascade sys level state x
        (Function.update state level (sys.flAdd (state level) x))
  | carry (level : Fin sys.levelCount) (state : Fin sys.levelCount → ℝ) (x : ℝ)
      (hover : sys.upper level ≤ sys.flAdd (state level) x)
      (hnext : level.val + 1 < sys.levelCount)
      {result : Fin sys.levelCount → ℝ}
      (next : P01AccumulatorCascade sys
        ⟨level.val + 1, hnext⟩ (Function.update state level 0)
        (sys.flAdd (state level) x) result) :
      P01AccumulatorCascade sys level state x result

/-- Process a list through the lowest accumulator, cascading when required. -/
inductive P01AccumulatorProcess
    (sys : P01AccumulatorSystem) : List ℝ →
      (Fin sys.levelCount → ℝ) → (Fin sys.levelCount → ℝ) → Prop
  | nil (state) : P01AccumulatorProcess sys [] state state
  | cons (x : ℝ) {xs : List ℝ} {start middle finish : Fin sys.levelCount → ℝ}
      (head : P01AccumulatorCascade sys ⟨0, sys.levelCount_pos⟩ start x middle)
      (tail : P01AccumulatorProcess sys xs middle finish) :
      P01AccumulatorProcess sys (x :: xs) start finish

/-- The generic Wolfe accumulator class: process all terms, then add the
accumulator levels in an order that the source leaves unspecified. -/
def P01AccumulatorEvaluation
    (sys : P01AccumulatorSystem) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ final : Fin sys.levelCount → ℝ,
    P01AccumulatorProcess sys inputs (fun _ => 0) final ∧
    ∃ ordered : List ℝ,
      ordered.Perm (List.ofFn final) ∧
      result = match ordered with
        | [] => 0
        | x :: rest => rest.foldl sys.flAdd x

/-- Malcolm's specialization: the final accumulator levels are recursively
summed in decreasing order of absolute value. -/
def P01MalcolmAccumulatorEvaluation
    (sys : P01AccumulatorSystem) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ final : Fin sys.levelCount → ℝ,
    P01AccumulatorProcess sys inputs (fun _ => 0) final ∧
    ∃ ordered : List ℝ,
      ordered.Perm (List.ofFn final) ∧
      (ordered.Pairwise fun x y => |y| ≤ |x|) ∧
      result = match ordered with
        | [] => 0
        | x :: rest => rest.foldl sys.flAdd x

/-- A distillation state preserves the exact sum and exposes a designated final component. -/
structure P01DistillationState where
  values : List ℝ

/-- The specification supplied for distillation algorithms; `isFloat` records
the paper's requirement that every iterate consists of floating-point numbers.
No transition rule is asserted. -/
def P01DistillationSpecification
    (isFloat : ℝ → Prop) (u : ℝ) (initial : List ℝ)
    (states : List P01DistillationState) : Prop :=
  0 ≤ u ∧
  states.head?.map P01DistillationState.values = some initial ∧
  (∀ state ∈ states,
    (∀ x ∈ state.values, isFloat x) ∧
    state.values.length = initial.length ∧ state.values.sum = initial.sum) ∧
  ∃ finalState : P01DistillationState,
    states.getLast? = some finalState ∧
    ∃ final : ℝ,
      finalState.values.getLast? = some final ∧
      |final - initial.sum| ≤ u * |initial.sum|

/-! ## Statistical estimates in section 4 -/

/-- The paper restates that worst-case propagation can make error bounds pessimistic. -/
structure P01WorstCasePropagationPessimismReport where
  concernsRoundingErrorBounds : Bool
  boundsAccountForWorstCaseErrorPropagation : Bool
  boundsCanBeVeryPessimisticForThatReason : Bool

def p01WorstCasePropagationPessimismReport :
    P01WorstCasePropagationPessimismReport :=
  { concernsRoundingErrorBounds := true
    boundsAccountForWorstCaseErrorPropagation := true
    boundsCanBeVeryPessimisticForThatReason := true }

/-- Motivation for using statistical estimates as an alternative comparison. -/
structure P01StatisticalAverageCaseMotivationReport where
  comparesSummationMethodsUsingStatisticalErrorEstimates : Bool
  estimatesMayBeMoreRepresentativeOfAverageCase : Bool

def p01StatisticalAverageCaseMotivationReport :
    P01StatisticalAverageCaseMotivationReport :=
  { comparesSummationMethodsUsingStatisticalErrorEstimates := true
    estimatesMayBeMoreRepresentativeOfAverageCase := true }

/-- Summation methods appearing in the statistical and experimental tables. -/
inductive P01SummationMethod
  | original | increasing | decreasing | psum | pairwise | insertion | plusMinus | compensated

/-- The eight summation options used throughout the section 6 experiments. -/
def p01EightSummationMethods : List P01SummationMethod :=
  [.original, .increasing, .decreasing, .psum, .insertion, .plusMinus, .pairwise,
    .compensated]

/-- Increasing-recursive sign-separated evaluation used in the section 6 experiments. -/
def P01IncreasingPlusMinusEvaluation
    (flAdd : ℝ → ℝ → ℝ) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ negatives nonnegatives : List ℝ,
    (negatives ++ nonnegatives).Perm inputs ∧
    (∀ x ∈ negatives, x < 0) ∧
    (∀ x ∈ nonnegatives, 0 ≤ x) ∧
    P01AbsNondecreasing negatives ∧ P01AbsNondecreasing nonnegatives ∧
    result = match negatives, nonnegatives with
      | [], [] => 0
      | [], _ => p01RecursiveList flAdd nonnegatives
      | _, [] => p01RecursiveList flAdd negatives
      | _, _ => flAdd
          (p01RecursiveList flAdd nonnegatives)
          (p01RecursiveList flAdd negatives)

/-- Model-neutral semantics of the eight section 6 summation options. -/
def P01SummationMethodEvaluation
    (flAdd : ℝ → ℝ → ℝ) (method : P01SummationMethod)
    {n : ℕ} (v : Fin n → ℝ) (result : ℝ) : Prop :=
  match method with
  | .original => result = p01RecursiveSum flAdd n v
  | .increasing => ∃ p : Equiv.Perm (Fin n),
      P01IncreasingMagnitude v p ∧
      result = p01RecursiveSum flAdd n (p01Permuted v p)
  | .decreasing => ∃ p : Equiv.Perm (Fin n),
      P01DecreasingMagnitude v p ∧
      result = p01RecursiveSum flAdd n (p01Permuted v p)
  | .psum => ∃ p : Equiv.Perm (Fin n),
      P01PsumOrder flAdd v p ∧
      result = p01RecursiveSum flAdd n (p01Permuted v p)
  | .pairwise => ∃ p : Equiv.Perm (Fin n),
      P01IncreasingMagnitude v p ∧
      P01PairwiseEvaluation flAdd (List.ofFn (p01Permuted v p)) result
  | .insertion => P01InsertionEvaluation flAdd (List.ofFn v) result
  | .plusMinus => P01IncreasingPlusMinusEvaluation flAdd (List.ofFn v) result
  | .compensated => result = p01CompensatedSum flAdd (List.ofFn v)

/-- The two nonnegative input distributions in Table 4.1. -/
inductive P01InputDistribution
  | uniform | exponential

/-- The five methods appearing in Table 4.1 (where `random` is an ordering). -/
inductive P01StatisticalMethod
  | increasing | random | decreasing | insertion | pairwise

/-- The probabilistic setup attributed to Robertazzi and Schwartz [35]. -/
structure P01StatisticalModelSpecification where
  distribution : P01InputDistribution
  inputsNonnegative : Bool
  inputMean : ℝ
  inputMean_pos : 0 < inputMean
  uniformLower : Option ℝ
  uniformUpper : Option ℝ
  exponentialMean : Option ℝ
  additionErrorsAreRelative : Bool
  additionErrorsIndependent : Bool
  additionErrorMean : ℝ
  additionErrorVariance : ℝ
  additionErrorVarianceIsFinite : Bool
  variousSimplifyingAssumptionsMade : Bool
  analysisAttributedToRobertazziAndSchwartz : Bool
  citationReference : ℕ
  meanSquareErrorDefinedAsVarianceOfAbsoluteError : Bool

noncomputable def p01StatisticalModelSpecification
    (distribution : P01InputDistribution) (μ σ : ℝ) (hμ : 0 < μ) :
    P01StatisticalModelSpecification :=
  { distribution := distribution
    inputsNonnegative := true
    inputMean := μ
    inputMean_pos := hμ
    uniformLower := match distribution with
      | .uniform => some 0
      | .exponential => none
    uniformUpper := match distribution with
      | .uniform => some (2 * μ)
      | .exponential => none
    exponentialMean := match distribution with
      | .uniform => none
      | .exponential => some μ
    additionErrorsAreRelative := true
    additionErrorsIndependent := true
    additionErrorMean := 0
    additionErrorVariance := σ ^ 2
    additionErrorVarianceIsFinite := true
    variousSimplifyingAssumptionsMade := true
    analysisAttributedToRobertazziAndSchwartz := true
    citationReference := 35
    meanSquareErrorDefinedAsVarianceOfAbsoluteError := true }

/-- The decimal coefficient reported in Table 4.1. -/
noncomputable def p01MSECoefficient :
    P01InputDistribution → P01StatisticalMethod → ℝ
  | .uniform, .increasing => 20 / 100
  | .uniform, .random => 33 / 100
  | .uniform, .decreasing => 53 / 100
  | .uniform, .insertion => 26 / 10
  | .uniform, .pairwise => 27 / 10
  | .exponential, .increasing => 13 / 100
  | .exponential, .random => 33 / 100
  | .exponential, .decreasing => 63 / 100
  | .exponential, .insertion => 26 / 10
  | .exponential, .pairwise => 4

/-- Power of `n` in the reported mean-square estimate. -/
def p01MSEPower : P01StatisticalMethod → ℕ
  | .increasing | .random | .decreasing => 3
  | .insertion | .pairwise => 2

/-- A Table 4.1 estimate, preserving its status as a reported statistical estimate. -/
noncomputable def p01ReportedMSE
    (distribution : P01InputDistribution) (method : P01StatisticalMethod)
    (μ σ : ℝ) (n : ℕ) : ℝ :=
  p01MSECoefficient distribution method * μ ^ 2 *
    (n : ℝ) ^ p01MSEPower method * σ ^ 2

/-- Interpretation that the recursive coefficient ranking agrees with equation (2.8). -/
structure P01Table41RecursiveRankingAgreementReport where
  appliesToNonnegativeInputs : Bool
  rankingOrdersIncreasingBeforeRandomBeforeDecreasing : Bool
  rankingReportedAsPreciselyThatGivenByEquation28 : Bool

def p01Table41RecursiveRankingAgreementReport :
    P01Table41RecursiveRankingAgreementReport :=
  { appliesToNonnegativeInputs := true
    rankingOrdersIncreasingBeforeRandomBeforeDecreasing := true
    rankingReportedAsPreciselyThatGivenByEquation28 := true }

/-- Source-facing insertion-versus-pairwise bound comparison below Table 4.1. -/
structure P01Table41InsertionPairwiseBoundSourceErrorReport where
  appliesToNonnegativeInputs : Bool
  concernsComputedRoundingErrorBounds : Bool
  insertionBoundAssertedNoLargerThanPairwise : Bool

def p01Table41InsertionPairwiseBoundSourceErrorReport :
    P01Table41InsertionPairwiseBoundSourceErrorReport :=
  { appliesToNonnegativeInputs := true
    concernsComputedRoundingErrorBounds := true
    insertionBoundAssertedNoLargerThanPairwise := true }

/-- Literal reported constants in the pairwise-versus-recursive bound comparison. -/
structure P01Table41PairwiseRecursiveBoundConstantReport where
  appliesToNonnegativeInputs : Bool
  pairwiseConstantReportedAsLogTwoN : Bool
  recursiveConstantReportedAsN : Bool
  pairwiseConstantReportedSmaller : Bool
  strictComparisonEndpointScopeSpecified : Bool

def p01Table41PairwiseRecursiveBoundConstantReport :
    P01Table41PairwiseRecursiveBoundConstantReport :=
  { appliesToNonnegativeInputs := true
    pairwiseConstantReportedAsLogTwoN := true
    recursiveConstantReportedAsN := true
    pairwiseConstantReportedSmaller := true
    strictComparisonEndpointScopeSpecified := false }

/-! ## The no-guard-digit model in section 5 -/

/-- Computed no-guard sum of the first `k+1` entries. -/
noncomputable def p01NoGuardRecursivePrefix
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ) (k : Fin n) : ℝ :=
  p01RecursiveSum fp.fl_add (k.val + 1) fun i => v ⟨i.val, by omega⟩

/-- Stepwise independent perturbations for recursive summation under (5.1). -/
def P01NoGuardRecursiveWitness
    (fp : NoGuardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (α β : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, 0 < k.val →
    |α k| ≤ fp.u ∧ |β k| ≤ fp.u ∧
    p01NoGuardRecursivePrefix fp n v k =
      p01NoGuardRecursivePrefix fp n v (p01PreviousIndex k) * (1 + α k) +
        v k * (1 + β k)

/-- The no-guard analogue of the product remainders in (2.3)--(2.5).
The first two inputs deliberately receive independent remainders. -/
def P01NoGuardThetaWitness
    (fp : NoGuardAddModel) (n : ℕ) (v θ : Fin n → ℝ) : Prop :=
  p01RecursiveSum fp.fl_add n v = ∑ i : Fin n, v i * (1 + θ i) ∧
  ∀ i : Fin n, |θ i| ≤ p01Gamma fp.u (p01RecursivePathLength n i)

/-- The no-guard replacement of (3.3): each internal-node error has the
two-input perturbation expansion analogous to (5.2). -/
def P01NoGuardTreeWitness
    (fp : NoGuardAddModel) : P01SumTree → Prop
  | .leaf _ => True
  | .node left right =>
      (∃ α β : ℝ,
        |α| ≤ fp.u ∧ |β| ≤ fp.u ∧
        P01SumTree.rounded fp.fl_add (.node left right) -
            P01SumTree.exact (.node left right) =
          (P01SumTree.rounded fp.fl_add left - P01SumTree.exact left) +
          (P01SumTree.rounded fp.fl_add right - P01SumTree.exact right) +
          P01SumTree.rounded fp.fl_add left * α +
          P01SumTree.rounded fp.fl_add right * β) ∧
      P01NoGuardTreeWitness fp left ∧ P01NoGuardTreeWitness fp right

/-- Same-sign test used literally by the modified no-guard correction. -/
def P01SameSign (x y : ℝ) : Prop :=
  (x = 0 ∧ y = 0) ∨ (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)

/-- Kahan's modified correction with the printed constant `0.46 = 23/50`. -/
noncomputable def p01NoGuardModifiedCorrection
    (flAdd flMul : ℝ → ℝ → ℝ) (temp s y : ℝ) : ℝ :=
  by
    classical
    let f :=
      if P01SameSign temp y then
        flAdd (flAdd (flMul (23 / 50 : ℝ) s) (-s)) s
      else 0
    exact flAdd (flAdd (flAdd temp (-f)) (-(flAdd s (-f)))) y

/-- One iteration of the modified compensated algorithm on printed page 793. -/
noncomputable def p01NoGuardModifiedStep
    (flAdd flMul : ℝ → ℝ → ℝ)
    (state : P01CompensatedState) (x : ℝ) : P01CompensatedState :=
  let temp := state.sum
  let y := flAdd x state.correction
  let s := flAdd temp y
  ⟨s, p01NoGuardModifiedCorrection flAdd flMul temp s y⟩

/-- Complete modified compensated summation using Kahan's no-guard correction. -/
noncomputable def p01NoGuardModifiedSum
    (flAdd flMul : ℝ → ℝ → ℝ) (inputs : List ℝ) : ℝ :=
  (inputs.foldl (p01NoGuardModifiedStep flAdd flMul) ⟨0, 0⟩).sum

/-! ## Numerical experiment records in section 6 -/

/-- One row entry from Tables 6.1--6.4: reported error, optional `T`, and optional `R`. -/
structure P01ExperimentMetrics where
  relativeError : ℚ
  runningMagnitude : Option ℚ
  normalizedError : Option ℚ

/-- A convenient constructor for exact rational encodings of printed decimals. -/
def p01Metrics (error : ℚ) (running normalized : Option ℚ) :
    P01ExperimentMetrics :=
  ⟨error, running, normalized⟩

/-- Interpretation of the two diagnostics printed with the a-priori tables. -/
structure P01ExperimentBoundSharpnessDiagnosticsReport where
  runningMagnitudeTIndicatesClosenessOfStrongestBoundToEquality : Bool
  normalizedRIndicatesClosenessOfWeakestBoundToEquality : Bool

def p01ExperimentBoundSharpnessDiagnosticsReport :
    P01ExperimentBoundSharpnessDiagnosticsReport :=
  { runningMagnitudeTIndicatesClosenessOfStrongestBoundToEquality := true
    normalizedRIndicatesClosenessOfWeakestBoundToEquality := true }

/-- The 64 Taylor terms used to approximate `exp (-2*pi)` in Table 6.1. -/
noncomputable def p01Table61Input (i : Fin 64) : ℝ :=
  (-2 * Real.pi) ^ i.val / (Nat.factorial i.val : ℝ)

/-- The unavailable random samples behind Table 6.2 are specified by distribution and size. -/
structure P01Table62SetupReport where
  standardNormalDistribution : Bool
  sampleSizes : List ℕ

def p01Table62SetupReport : P01Table62SetupReport :=
  { standardNormalDistribution := true
    sampleSizes := [2048, 4096] }

/-- The positive inverse-square family used in Table 6.3. -/
noncomputable def p01Table63Input (n : ℕ) (i : Fin n) : ℝ :=
  1 / ((i.val + 1 : ℕ) : ℝ) ^ 2

/-- The `n` equally spaced inputs on `[1,2]` used in Table 6.4. -/
noncomputable def p01Table64Input (n : ℕ) (i : Fin n) : ℝ :=
  1 + (i.val : ℝ) / (n - 1 : ℕ)

/-- Table 6.1: 64 terms of the Taylor expansion of `exp(-2*pi)`. -/
def p01Table61 : P01SummationMethod → P01ExperimentMetrics
  | .original => p01Metrics (511 / 1000000) (some 268) (some (149 / 10000))
  | .increasing => p01Metrics (227 / 100000) (some 297) (some (664 / 10000))
  | .decreasing => p01Metrics (185 / 1000000000) (some 297) (some (540 / 100000000))
  | .psum => p01Metrics (227 / 100000) (some 285) (some (664 / 10000))
  | .pairwise => p01Metrics (141 / 1000000) (some (868 / 10)) (some (413 / 100000))
  | .insertion => p01Metrics (227 / 100000) (some 297) (some (664 / 10000))
  | .plusMinus => p01Metrics (186 / 10000) (some 1340) (some (544 / 1000))
  | .compensated => p01Metrics (511 / 1000000) none (some (149 / 10000))

/-- Shared data and method scope for the Table 6.1 prose diagnostics. -/
structure P01Table61ExperimentScope where
  input : Fin 64 → ℝ
  methods : List P01SummationMethod

noncomputable def p01Table61ExperimentScope : P01Table61ExperimentScope :=
  { input := p01Table61Input
    methods := p01EightSummationMethods }

/-- The source identifies the Table 6.1 data as 64 Taylor terms for exp(-2*pi). -/
structure P01Table61InputDescriptionReport where
  scope : P01Table61ExperimentScope
  termCount : ℕ
  inputIsTaylorExpansionOfExpNegativeTwoPi : Bool

noncomputable def p01Table61InputDescriptionReport :
    P01Table61InputDescriptionReport :=
  { scope := p01Table61ExperimentScope
    termCount := 64
    inputIsTaylorExpansionOfExpNegativeTwoPi := true }

/-- The source describes the cancellation in the Table 6.1 sum as severe. -/
structure P01Table61SevereCancellationReport where
  scope : P01Table61ExperimentScope
  severeCancellation : Bool

noncomputable def p01Table61SevereCancellationReport :
    P01Table61SevereCancellationReport :=
  { scope := p01Table61ExperimentScope
    severeCancellation := true }

/-- The decreasing order is reported to let the smallest-modulus terms contribute fully. -/
structure P01Table61DecreasingSmallTermContributionReport where
  scope : P01Table61ExperimentScope
  method : P01SummationMethod
  letsSmallestTermsContributeFully : Bool

noncomputable def p01Table61DecreasingSmallTermContributionReport :
    P01Table61DecreasingSmallTermContributionReport :=
  { scope := p01Table61ExperimentScope
    method := .decreasing
    letsSmallestTermsContributeFully := true }

/-- The other Table 6.1 methods are reported to swamp the small terms. -/
structure P01Table61OtherMethodsSwampingReport where
  scope : P01Table61ExperimentScope
  methods : List P01SummationMethod
  methodsSwampSmallTerms : Bool

noncomputable def p01Table61OtherMethodsSwampingReport :
    P01Table61OtherMethodsSwampingReport :=
  { scope := p01Table61ExperimentScope
    methods := [.original, .increasing, .psum, .pairwise, .insertion, .plusMinus,
      .compensated]
    methodsSwampSmallTerms := true }

/-- The first four Table 6.1 running-magnitude values are reported to have similar size. -/
structure P01Table61FirstFourRunningMagnitudeSimilarityReport where
  scope : P01Table61ExperimentScope
  methods : List P01SummationMethod
  runningMagnitudeValuesHaveSimilarMagnitude : Bool
  similarityReportedAsReasonRunningMagnitudeBoundMissesDecreasingOrderMerit : Bool

noncomputable def p01Table61FirstFourRunningMagnitudeSimilarityReport :
    P01Table61FirstFourRunningMagnitudeSimilarityReport :=
  { scope := p01Table61ExperimentScope
    methods := [.original, .increasing, .decreasing, .psum]
    runningMagnitudeValuesHaveSimilarMagnitude := true
    similarityReportedAsReasonRunningMagnitudeBoundMissesDecreasingOrderMerit := true }

/-- The running-magnitude bounds are reported not to expose the merit of decreasing order. -/
structure P01Table61RunningMagnitudeBoundLimitationReport where
  scope : P01Table61ExperimentScope
  diagnosticIsRunningMagnitudeT : Bool
  meritOfDecreasingOrderReflected : Bool

noncomputable def p01Table61RunningMagnitudeBoundLimitationReport :
    P01Table61RunningMagnitudeBoundLimitationReport :=
  { scope := p01Table61ExperimentScope
    diagnosticIsRunningMagnitudeT := true
    meritOfDecreasingOrderReflected := false }

/-- The plus/minus method is reported to lose one additional correct significant figure. -/
structure P01Table61PlusMinusDigitLossAmountReport where
  scope : P01Table61ExperimentScope
  method : P01SummationMethod
  additionalCorrectSignificantFiguresLost : ℕ

noncomputable def p01Table61PlusMinusDigitLossAmountReport :
    P01Table61PlusMinusDigitLossAmountReport :=
  { scope := p01Table61ExperimentScope
    method := .plusMinus
    additionalCorrectSignificantFiguresLost := 1 }

/-- The reported one-figure loss is relative to every other Table 6.1 method. -/
structure P01Table61PlusMinusDigitLossComparisonReport where
  scope : P01Table61ExperimentScope
  method : P01SummationMethod
  comparisonMethods : List P01SummationMethod

noncomputable def p01Table61PlusMinusDigitLossComparisonReport :
    P01Table61PlusMinusDigitLossComparisonReport :=
  { scope := p01Table61ExperimentScope
    method := .plusMinus
    comparisonMethods := [.original, .increasing, .decreasing, .psum, .pairwise,
      .insertion, .compensated] }

/-- The source says the plus/minus digit loss is predicted by its running-magnitude value. -/
structure P01Table61PlusMinusRunningMagnitudePredictionReport where
  scope : P01Table61ExperimentScope
  method : P01SummationMethod
  diagnosticIsRunningMagnitudeT : Bool
  predictedObservationIsOneAdditionalCorrectSignificantFigureLost : Bool
  diagnosticReportedToPredictDigitLoss : Bool

noncomputable def p01Table61PlusMinusRunningMagnitudePredictionReport :
    P01Table61PlusMinusRunningMagnitudePredictionReport :=
  { scope := p01Table61ExperimentScope
    method := .plusMinus
    diagnosticIsRunningMagnitudeT := true
    predictedObservationIsOneAdditionalCorrectSignificantFigureLost := true
    diagnosticReportedToPredictDigitLoss := true }

/-- Table 6.2, for `n=2048` standard-normal inputs. -/
def p01Table62_2048 : P01SummationMethod → P01ExperimentMetrics
  | .original => p01Metrics (747 / 100000000) (some 30600) (some (506 / 1000))
  | .increasing => p01Metrics (332 / 100000000) (some 15300) (some (225 / 1000))
  | .decreasing => p01Metrics (717 / 100000000) (some 26500) (some (486 / 1000))
  | .psum => p01Metrics (682 / 10000000000) (some 826) (some (462 / 100000))
  | .pairwise => p01Metrics (660 / 1000000000) (some 2870) (some (447 / 10000))
  | .insertion => p01Metrics (512 / 1000000000) (some 2320) (some (347 / 10000))
  | .plusMinus => p01Metrics (120 / 1000000) (some 480000) (some (815 / 100))
  | .compensated => p01Metrics (228 / 1000000000) none (some (154 / 10000))

/-- Table 6.2, for `n=4096` standard-normal inputs. -/
def p01Table62_4096 : P01SummationMethod → P01ExperimentMetrics
  | .original => p01Metrics (806 / 100000000) (some 66900) (some (235 / 1000))
  | .increasing => p01Metrics (104 / 10000000) (some 47400) (some (304 / 1000))
  | .decreasing => p01Metrics (184 / 100000000) (some 42800) (some (538 / 10000))
  | .psum => p01Metrics (266 / 10000000000) (some 1680) (some (776 / 1000000))
  | .pairwise => p01Metrics (138 / 1000000000) (some 5700) (some (404 / 100000))
  | .insertion => p01Metrics (687 / 1000000000) (some 5380) (some (200 / 10000))
  | .plusMinus => p01Metrics (368 / 1000000) (some 2020000) (some (107 / 10))
  | .compensated => p01Metrics (192 / 1000000000) none (some (559 / 100000))

/-- Presence of cancellation in both Table 6.2 standard-normal sums. -/
structure P01Table62CancellationPresenceReport where
  bothTable62SumsHaveCancellation : Bool

def p01Table62CancellationPresenceReport :
    P01Table62CancellationPresenceReport :=
  { bothTable62SumsHaveCancellation := true }

/-- Severity comparison between Table 6.2 cancellation and the Taylor example. -/
structure P01Table62CancellationRelativeSeverityReport where
  comparisonReferenceIsTable61TaylorSum : Bool
  cancellationReportedLessSevereThanInTable61 : Bool

def p01Table62CancellationRelativeSeverityReport :
    P01Table62CancellationRelativeSeverityReport :=
  { comparisonReferenceIsTable61TaylorSum := true
    cancellationReportedLessSevereThanInTable61 := true }

/-- Running-magnitude diagnostic interpretation for the Table 6.2 ranking. -/
structure P01Table62RunningMagnitudeRankingPredictionReport where
  reportedBestMethodIsPsum : Bool
  reportedWorstMethodIsPlusMinus : Bool
  rankingReportedReflectedByRunningMagnitudeTValues : Bool

def p01Table62RunningMagnitudeRankingPredictionReport :
    P01Table62RunningMagnitudeRankingPredictionReport :=
  { reportedBestMethodIsPsum := true
    reportedWorstMethodIsPlusMinus := true
    rankingReportedReflectedByRunningMagnitudeTValues := true }

/-- One row of Table 6.3. -/
structure P01Table63Row where
  n : ℕ
  increasingError : ℚ
  decreasingError : ℚ

/-- Table 6.3: increasing and decreasing errors for `x_i=1/i^2`. -/
def p01Table63 : List P01Table63Row :=
  [ ⟨500, 104 / 1000000000, 331 / 1000000000⟩,
    ⟨1000, 101 / 1000000000, 624 / 1000000000⟩,
    ⟨2000, 174 / 10000000000, 564 / 100000000⟩,
    ⟨3000, 522 / 10000000000, 230 / 10000000⟩,
    ⟨4000, 136 / 1000000000, 277 / 10000000⟩,
    ⟨5000, 390 / 10000000000, 581 / 10000000⟩ ]

/-- Empirical decreasing-order accuracy trend in Table 6.3. -/
structure P01Table63DecreasingAccuracyObservationReport where
  concernsLargeLengthsInInverseSquareExperiment : Bool
  decreasingOrderingReportedMuchLessAccurateThanIncreasing : Bool

def p01Table63DecreasingAccuracyObservationReport :
    P01Table63DecreasingAccuracyObservationReport :=
  { concernsLargeLengthsInInverseSquareExperiment := true
    decreasingOrderingReportedMuchLessAccurateThanIncreasing := true }

/-- Section-2-bound explanation of the Table 6.3 observation. -/
structure P01Table63SectionTwoBoundsExpectationReport where
  concernsDecreasingLessAccurateObservationAtLargeLengths : Bool
  outcomeReportedExpectedFromSectionTwoErrorBounds : Bool

def p01Table63SectionTwoBoundsExpectationReport :
    P01Table63SectionTwoBoundsExpectationReport :=
  { concernsDecreasingLessAccurateObservationAtLargeLengths := true
    outcomeReportedExpectedFromSectionTwoErrorBounds := true }

/-- Table 6.4 at `n=2048`, for inputs equally spaced on `[1,2]`. -/
def p01Table64_2048 : P01SummationMethod → Option P01ExperimentMetrics
  | .increasing => some (p01Metrics (286 / 100000000) (some 2800000) (some 24))
  | .decreasing => some (p01Metrics (386 / 10000000) (some 3500000) (some 324))
  | .pairwise => some (p01Metrics (159 / 1000000000) (some 33800) (some (133 / 100)))
  | .compensated => some (p01Metrics 0 none (some 0))
  | _ => none

/-- Table 6.4 at `n=4096`. -/
def p01Table64_4096 : P01SummationMethod → Option P01ExperimentMetrics
  | .increasing => some (p01Metrics (335 / 10000000) (some 11200000) (some 281))
  | .decreasing => some (p01Metrics (218 / 10000000) (some 14000000) (some 183))
  | .pairwise => some (p01Metrics (159 / 1000000000) (some 73700) (some (133 / 100)))
  | .compensated => some (p01Metrics 0 none (some 0))
  | _ => none

/-- Length scope of the experiments on equally spaced inputs in [1,2]. -/
structure P01Table64TestedLengthScopeReport where
  concernsInputsEquallySpacedOnOneTwo : Bool
  variousLengthsTested : Bool
  inclusiveUpperLength : ℕ

def p01Table64TestedLengthScopeReport : P01Table64TestedLengthScopeReport :=
  { concernsInputsEquallySpacedOnOneTwo := true
    variousLengthsTested := true
    inclusiveUpperLength := 4096 }

/-- Reported increasing-versus-decreasing observation over the Table 6.4 family. -/
structure P01Table64IncreasingDecreasingDifferenceReport where
  concernsTestedEquallySpacedOneTwoFamily : Bool
  greatDifferenceObserved : Bool

def p01Table64IncreasingDecreasingDifferenceReport :
    P01Table64IncreasingDecreasingDifferenceReport :=
  { concernsTestedEquallySpacedOneTwoFamily := true
    greatDifferenceObserved := false }

/-- Insertion was reported equivalent to pairwise for the Table 6.4 family. -/
structure P01Table64InsertionPairwiseEquivalenceReport where
  concernsTestedEquallySpacedOneTwoFamily : Bool
  insertionReportedEquivalentToPairwise : Bool

def p01Table64InsertionPairwiseEquivalenceReport :
    P01Table64InsertionPairwiseEquivalenceReport :=
  { concernsTestedEquallySpacedOneTwoFamily := true
    insertionReportedEquivalentToPairwise := true }

/-- Compensated summation had zero error at every tried Table 6.4 length. -/
structure P01Table64CompensatedAllTriedZeroReport where
  concernsTestedEquallySpacedOneTwoFamily : Bool
  appliesToEveryTriedLength : Bool
  compensatedErrorReportedZero : Bool

def p01Table64CompensatedAllTriedZeroReport :
    P01Table64CompensatedAllTriedZeroReport :=
  { concernsTestedEquallySpacedOneTwoFamily := true
    appliesToEveryTriedLength := true
    compensatedErrorReportedZero := true }

/-- Explanation offered for the small increasing-versus-decreasing difference. -/
structure P01Table64MagnitudeVariationExplanationReport where
  concernsSmallObservedIncreasingDecreasingDifference : Bool
  inputMagnitudesVaryLittle : Bool
  smallDifferenceReportedExpectedForThatReason : Bool

def p01Table64MagnitudeVariationExplanationReport :
    P01Table64MagnitudeVariationExplanationReport :=
  { concernsSmallObservedIncreasingDecreasingDifference := true
    inputMagnitudesVaryLittle := true
    smallDifferenceReportedExpectedForThatReason := true }

/-- The two right-hand-side systems in Table 6.5. -/
inductive P01ForwardSystem
  | first | second

/-- Table 6.5's two rows of forward-substitution forward errors. -/
def p01Table65 : P01ForwardSystem → P01SummationMethod → ℚ
  | .first, .original => 301 / 1000000
  | .first, .increasing => 118 / 10000
  | .first, .decreasing => 770 / 100000
  | .first, .psum => 118 / 10000
  | .first, .pairwise => 294 / 10000
  | .first, .insertion => 118 / 10000
  | .first, .plusMinus => 401 / 100000
  | .first, .compensated => 770 / 100000
  | .second, .original => 131 / 10000
  | .second, .increasing => 264 / 10000
  | .second, .decreasing => 463 / 100000
  | .second, .psum => 264 / 10000
  | .second, .pairwise => 681 / 1000000
  | .second, .insertion => 106 / 10000
  | .second, .plusMinus => 264 / 10000
  | .second, .compensated => 204 / 10000

/-- One reported function-value-only MDS run. Values are the printed rounded data. -/
structure P01MDSReport where
  dimension : ℕ
  method : P01SummationMethod
  start : List ℚ
  earlierAttemptStart : Option (List ℚ)
  earlierRunFromFirstStartingValueMadeLittleProgress : Option Bool
  evaluations : ℕ
  located : List ℚ
  objective : ℚ
  computedSum : ℚ
  referenceSum : ℚ
  locatedVectorQuotedToSevenSignificantFigures : Bool
  sumsQuotedToFiveSignificantFigures : Bool

/-- The increasing-recursive MDS report on printed page 795. -/
def p01MDSIncreasingReport : P01MDSReport :=
  { dimension := 3
    method := .increasing
    start := [1 / 3, 2 / 3, 1]
    earlierAttemptStart := none
    earlierRunFromFirstStartingValueMadeLittleProgress := none
    evaluations := 280
    located := [4975987 / 1000000, -2495094 / 1000000, -2480894 / 1000000]
    objective := 1
    computedSum := -95367 / 100000000000
    referenceSum := -47684 / 100000000000
    locatedVectorQuotedToSevenSignificantFigures := true
    sumsQuotedToFiveSignificantFigures := true }

/-- The compensated-summation MDS report on printed page 795. -/
def p01MDSCompensatedReport : P01MDSReport :=
  { dimension := 3
    method := .compensated
    start := [-1 / 3, 0, 2 / 3]
    earlierAttemptStart := some [1 / 3, 2 / 3, 1]
    earlierRunFromFirstStartingValueMadeLittleProgress := some true
    evaluations := 166
    located := [-8308306 / 10000000, -7626623 / 10000000, 1593493 / 1000000]
    objective := 1
    computedSum := 23842 / 100000000000
    referenceSum := 11921 / 100000000000
    locatedVectorQuotedToSevenSignificantFigures := true
    sumsQuotedToFiveSignificantFigures := true }

/-- The Vandermonde entries used in the forward-substitution experiment. -/
noncomputable def p01Vandermonde10 (i j : Fin 10) : ℝ :=
  (((j.val : ℝ) / 9) ^ i.val)

/-- Two exact endpoint-spaced vectors from the forward-substitution experiment. -/
noncomputable def p01ForwardInput (system : P01ForwardSystem) (i : Fin 10) : ℝ :=
  match system with
  | .first => 1 + (99 : ℝ) * i.val / 9
  | .second => (100 : ℝ) * i.val / 9

/-- Final-factor characterization of LU factorization with partial pivoting.
Unit-lower normalization and `|L i k| ≤ 1` encode the maximal-pivot choice. -/
def P01PartialPivotingLU {n : ℕ}
    (A P L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ perm : Equiv.Perm (Fin n), ∀ i j,
      P i j = if j = perm i then 1 else 0) ∧
  (∀ i j, i.val < j.val → L i j = 0) ∧
  (∀ i, L i i = 1) ∧
  (∀ i j, j.val < i.val → U i j = 0) ∧
  (∀ i, U i i ≠ 0) ∧
  (∀ i k, k.val < i.val → |L i k| ≤ 1) ∧
  ∀ i j, ∑ k : Fin n, P i k * A k j = ∑ k : Fin n, L i k * U k j

/-- The source's separate limitation of the column-oriented substitution form. -/
structure P01ForwardColumnOrientedLimitationReport where
  amenableToVaryingSummationMethod : Bool

def p01ForwardColumnOrientedLimitationReport :
    P01ForwardColumnOrientedLimitationReport :=
  { amenableToVaryingSummationMethod := false }

/-- The matrix and right-hand-side relations defining the forward-substitution test. -/
def P01ForwardExperimentSetup
    (P L U T : Matrix (Fin 10) (Fin 10) ℝ)
    (b : P01ForwardSystem → Fin 10 → ℝ) : Prop :=
  P01PartialPivotingLU p01Vandermonde10 P L U ∧
  T = U.transpose ∧
  ∀ system, b system = T.mulVec (p01ForwardInput system)

/-- Scope of the forward-substitution measurements performed for Table 6.5. -/
structure P01ForwardSubstitutionMeasurementScopeReport where
  usesSimulatedSinglePrecision : Bool
  summationOptions : List P01SummationMethod
  forwardErrorEvaluatedForEveryOption : Bool

def p01ForwardSubstitutionMeasurementScopeReport :
    P01ForwardSubstitutionMeasurementScopeReport :=
  { usesSimulatedSinglePrecision := true
    summationOptions := p01EightSummationMethods
    forwardErrorEvaluatedForEveryOption := true }

/-- Inner-product forward substitution with one of the eight summation methods.

Products, the subtraction, and the division are all rounded in the same
23-significant-bit binary model used for the simulated-single experiments.
-/
def P01ForwardSubstitutionEvaluation
    (fp : P01BinaryRoundModel) (method : P01SummationMethod)
    (T : Matrix (Fin 10) (Fin 10) ℝ)
    (b computed : Fin 10 → ℝ) : Prop :=
  fp.precision = 23 ∧
  (∀ i j, P01BaseTwoRepresentable fp.precision (T i j)) ∧
  (∀ i, P01BaseTwoRepresentable fp.precision (b i)) ∧
  (∀ i : Fin 10, T i i ≠ 0) ∧
  ∀ i : Fin 10, ∃ inner : ℝ,
    P01SummationMethodEvaluation (p01RoundAdd fp) method
      (fun j : Fin i.val =>
        fp.round
          (T i ⟨j.val, lt_trans j.isLt i.isLt⟩ *
            computed ⟨j.val, lt_trans j.isLt i.isLt⟩))
      inner ∧
    computed i = fp.round (fp.round (b i - inner) / T i i)

/-- The vector infinity norm used in the reported triangular-system condition number. -/
noncomputable def p01VectorInfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun i : Fin n => |x i|)

/-- The matrix infinity norm, the largest absolute row sum. -/
noncomputable def p01MatrixInfNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Set.range fun i : Fin n => ∑ j : Fin n, |A i j|)

/-- `κ∞(T) = ‖T‖∞ ‖T⁻¹‖∞`, with the inverse supplied explicitly. -/
noncomputable def p01NormwiseMatrixCondition
    {n : ℕ} (T Tinv : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  p01MatrixInfNorm T * p01MatrixInfNorm Tinv

/-- The componentwise condition number `cond(T,x)` printed before Table 6.5. -/
noncomputable def p01ComponentwiseTriangularCondition
    {n : ℕ} (T Tinv : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  let weighted : Fin n → ℝ := fun i =>
    ∑ j : Fin n, |T i j| * |x j|
  let propagated : Fin n → ℝ := fun i =>
    ∑ j : Fin n, |Tinv i j| * weighted j
  p01VectorInfNorm propagated / p01VectorInfNorm x

/-- The vector relative forward error introduced for triangular systems. -/
noncomputable def p01ForwardRelativeError
    {n : ℕ} (computed exact : Fin n → ℝ) : ℝ :=
  p01VectorInfNorm (computed - exact) / p01VectorInfNorm exact

/-- The paired forward-error variation factors for the two Table 6.5 systems. -/
structure P01ForwardErrorVariationFactorsReport where
  firstSystem : P01ForwardSystem
  firstSystemFactor : ℕ
  secondSystem : P01ForwardSystem
  secondSystemFactor : ℕ
  comparedMethods : List P01SummationMethod
  factorsMeasureVariationAcrossTable65ForwardErrors : Bool

def p01ForwardErrorVariationFactorsReport : P01ForwardErrorVariationFactorsReport :=
  { firstSystem := .first
    firstSystemFactor := 98
    secondSystem := .second
    secondSystemFactor := 39
    comparedMethods := p01EightSummationMethods
    factorsMeasureVariationAcrossTable65ForwardErrors := true }

/-- The two reported factors were the largest in a broader test set. -/
structure P01ForwardLargestObservedVariationReport where
  testsIncludedVariedMatricesAndRightHandSides : Bool
  tableFactorsWereLargestObservedVariations : Bool

def p01ForwardLargestObservedVariationReport :
    P01ForwardLargestObservedVariationReport :=
  { testsIncludedVariedMatricesAndRightHandSides := true
    tableFactorsWereLargestObservedVariations := true }

/-- No best-or-worst summation-method pattern was observed across those tests. -/
structure P01ForwardMethodRankingPatternReport where
  concernsSmallestAndLargestForwardErrors : Bool
  consistentMethodPatternObservedAcrossTests : Bool

def p01ForwardMethodRankingPatternReport : P01ForwardMethodRankingPatternReport :=
  { concernsSmallestAndLargestForwardErrors := true
    consistentMethodPatternObservedAcrossTests := false }

/-- Reported sensitivity of forward substitution to inner-product summation. -/
structure P01ForwardSubstitutionSensitivityReport where
  concernsSummationMethodForInnerProductEvaluation : Bool
  choiceCanSignificantlyAffectForwardSubstitutionAccuracy : Bool

def p01ForwardSubstitutionSensitivityReport :
    P01ForwardSubstitutionSensitivityReport :=
  { concernsSummationMethodForInnerProductEvaluation := true
    choiceCanSignificantlyAffectForwardSubstitutionAccuracy := true }

/-- The forward-substitution sensitivity is said to apply a fortiori to an LU solve. -/
structure P01FullLUSolveSensitivityImplicationReport where
  premiseIsForwardSubstitutionSensitivity : Bool
  conclusionAppliesAFortioriToFullLUSystemSolution : Bool

def p01FullLUSolveSensitivityImplicationReport :
    P01FullLUSolveSensitivityImplicationReport :=
  { premiseIsForwardSubstitutionSensitivity := true
    conclusionAppliesAFortioriToFullLUSystemSolution := true }

/-- Reported lack of a straightforward method predictor for a given linear system. -/
structure P01ForwardBestMethodPredictorReport where
  predictionTargetIsBestSummationMethodForGivenLinearSystem : Bool
  straightforwardPredictorAppearsToExist : Bool

def p01ForwardBestMethodPredictorReport : P01ForwardBestMethodPredictorReport :=
  { predictionTargetIsBestSummationMethodForGivenLinearSystem := true
    straightforwardPredictorAppearsToExist := false }

/-- The resulting practical recommendation for a general linear-equation solver. -/
structure P01ForwardNaturalRecursiveRecommendationReport where
  appliesToInnerProductsInGeneralLinearEquationSolvers : Bool
  recommendsRecursiveSummationInNaturalOrder : Bool

def p01ForwardNaturalRecursiveRecommendationReport :
    P01ForwardNaturalRecursiveRecommendationReport :=
  { appliesToInnerProductsInGeneralLinearEquationSolvers := true
    recommendsRecursiveSummationInNaturalOrder := true }

/-- MATLAB/IEEE-double arithmetic used for all experiments, with the printed
unit-roundoff value retained as an untoleranced approximation. -/
structure P01MatlabDoubleUnitRoundoffApproximationReport where
  allExperimentsReportedDoneUsingMATLAB : Bool
  matlabCitationReference : ℕ
  matlabReportedToUseIEEEStandardDoublePrecisionArithmetic : Bool
  reportedApproximateValue : ℚ
  approximationToleranceSpecified : Bool

def p01MatlabDoubleUnitRoundoffApproximationReport :
    P01MatlabDoubleUnitRoundoffApproximationReport :=
  { allExperimentsReportedDoneUsingMATLAB := true
    matlabCitationReference := 30
    matlabReportedToUseIEEEStandardDoublePrecisionArithmetic := true
    reportedApproximateValue := 11 / 100000000000000000
    approximationToleranceSpecified := false }

/-- A standard addition model carrying the source-visible MATLAB-double
reference-sum role and its separate untoleranced roundoff report. -/
structure P01MatlabDoubleReferenceArithmetic where
  addModel : P01StandardAddModel
  usedToComputeAprioriReferenceSums : Bool
  reportedAsMATLABDoubleArithmetic : Bool
  reportedApproximationConcernsAddModelUnitRoundoff : Bool
  sourceRole :
    usedToComputeAprioriReferenceSums = true ∧
      reportedAsMATLABDoubleArithmetic = true ∧
      reportedApproximationConcernsAddModelUnitRoundoff = true
  unitRoundoffReport : P01MatlabDoubleUnitRoundoffApproximationReport
  unitRoundoffReport_eq :
    unitRoundoffReport = p01MatlabDoubleUnitRoundoffApproximationReport

/-- The exact simulated-single unit roundoff printed at the section 6 page break. -/
noncomputable def p01SingleUnitRoundoff : ℝ := (2 : ℝ) ^ (-23 : ℤ)

/-- The separate untoleranced decimal approximation to simulated-single roundoff. -/
structure P01SimulatedSingleUnitRoundoffApproximationReport where
  exactUnitRoundoff : ℝ
  reportedApproximateValue : ℚ
  approximationToleranceSpecified : Bool

noncomputable def p01SimulatedSingleUnitRoundoffApproximationReport :
    P01SimulatedSingleUnitRoundoffApproximationReport :=
  { exactUnitRoundoff := p01SingleUnitRoundoff
    reportedApproximateValue := 12 / 100000000
    approximationToleranceSpecified := false }

/-- Arithmetic protocol used to simulate single precision in the a-priori tests. -/
structure P01SimulatedSingleArithmeticReport where
  significantBits : ℕ
  roundsResultOfEveryArithmeticOperation : Bool

def p01SimulatedSingleArithmeticReport : P01SimulatedSingleArithmeticReport :=
  { significantBits := 23
    roundsResultOfEveryArithmeticOperation := true }

/-- The relative-error metric printed before Table 6.1. -/
noncomputable def p01ReportedRelativeError (computed exact : ℝ) : ℝ :=
  |computed - exact| / |exact|

/-- The normalized `R` metric printed before Table 6.1. -/
noncomputable def p01ReportedNormalizedError
    (u computed exact absoluteInputSum : ℝ) : ℝ :=
  |computed - exact| / (u * absoluteInputSum)

/-! ## Remaining precise cross-cutting claims and symbolic examples -/

/-- Status-preserving form of the claimed Psum/increasing identity for one-signed data.

The source does not specify how either ordering resolves rounded ties, so literal equality of
the two nondeterministic ordering relations would be false without an invented convention.
-/
structure P01PsumOneSignedIdentityReport where
  appliesWhenAllInputsHaveOneSign : Bool
  orderingsClaimedIdentical : Bool
  tieBreakingSpecifiedBySource : Bool

def p01PsumOneSignedIdentityReport : P01PsumOneSignedIdentityReport :=
  { appliesWhenAllInputsHaveOneSign := true
    orderingsClaimedIdentical := true
    tieBreakingSpecifiedBySource := false }

/-- The actual error displayed for the near-attainability family. -/
noncomputable def p01NearAttainabilityActualError (r t : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(t : ℤ)) * ((4 : ℝ) ^ r - 1) / 3

/-- Bound (2.6) specialized to the near-attainability family. -/
noncomputable def p01NearAttainabilityEq26Bound (r t : ℕ) : ℝ :=
  p01Gamma ((2 : ℝ) ^ (-(t : ℤ))) (2 ^ r - 1) *
    p01AbsoluteSum (2 ^ r) (p01NearAttainabilityInput r t)

/-- The looser intermediate upper expression displayed after the equation-(2.6) bound. -/
noncomputable def p01NearAttainabilityEq26UpperExpression (r t : ℕ) : ℝ :=
  let n : ℝ := (2 ^ r : ℕ)
  let u : ℝ := (2 : ℝ) ^ (-(t : ℤ))
  (n * u) / (1 - n * u) * n

/-- Untoleranced approximation printed for the intermediate upper expression. -/
structure P01NearAttainabilityEq26UpperExpressionApproximationReport where
  approximatedExpression : ℕ → ℕ → ℝ
  comparisonExpression : ℕ → ℕ → ℝ
  reportedApproximatelyEqual : Bool
  approximationToleranceSpecified : Bool

noncomputable def p01NearAttainabilityEq26UpperExpressionApproximationReport :
    P01NearAttainabilityEq26UpperExpressionApproximationReport :=
  { approximatedExpression := p01NearAttainabilityEq26UpperExpression
    comparisonExpression := fun r t => (2 : ℝ) ^ (-(t : ℤ)) * (4 : ℝ) ^ r
    reportedApproximatelyEqual := true
    approximationToleranceSpecified := false }

/-- The sharper order-dependent bound (2.5) for the printed input order. -/
noncomputable def p01NearAttainabilityEq25Bound (r t : ℕ) : ℝ :=
  p01Eq25Budget ((2 : ℝ) ^ (-(t : ℤ)))
    (p01NearAttainabilityInput r t) (Equiv.refl (Fin (2 ^ r)))

/-- Bound (2.8), using the printed computed prefixes `S_hat_k = k`. -/
noncomputable def p01NearAttainabilityEq28Bound (r t : ℕ) : ℝ :=
  let u := (2 : ℝ) ^ (-(t : ℤ))
  u / (1 - u) *
    ∑ k : Fin (2 ^ r), if 0 < k.val then (k.val + 1 : ℕ) else 0

/-- Status form of one factor-three comparison in the near-attainability example. -/
structure P01NearAttainabilityFactorThreeReport where
  actualError : ℕ → ℕ → ℝ
  comparedBound : ℕ → ℕ → ℝ
  appliesUnderRMuchSmallerThanT : Bool
  reportedFactor : ℕ
  boundReportedWithinFactorOfActualError : Bool
  quantitativeSeparationSpecified : Bool

noncomputable def p01NearAttainabilityEq26FactorThreeReport :
    P01NearAttainabilityFactorThreeReport :=
  { actualError := p01NearAttainabilityActualError
    comparedBound := p01NearAttainabilityEq26Bound
    appliesUnderRMuchSmallerThanT := true
    reportedFactor := 3
    boundReportedWithinFactorOfActualError := true
    quantitativeSeparationSpecified := false }

noncomputable def p01NearAttainabilityEq25FactorThreeReport :
    P01NearAttainabilityFactorThreeReport :=
  { actualError := p01NearAttainabilityActualError
    comparedBound := p01NearAttainabilityEq25Bound
    appliesUnderRMuchSmallerThanT := true
    reportedFactor := 3
    boundReportedWithinFactorOfActualError := true
    quantitativeSeparationSpecified := false }

noncomputable def p01NearAttainabilityEq28FactorThreeReport :
    P01NearAttainabilityFactorThreeReport :=
  { actualError := p01NearAttainabilityActualError
    comparedBound := p01NearAttainabilityEq28Bound
    appliesUnderRMuchSmallerThanT := true
    reportedFactor := 3
    boundReportedWithinFactorOfActualError := true
    quantitativeSeparationSpecified := false }

/-- Status form of one smaller-bound comparison in the near-attainability example. -/
structure P01NearAttainabilitySmallerBoundReport where
  comparedBound : ℕ → ℕ → ℝ
  referenceEquation26Bound : ℕ → ℕ → ℝ
  referenceDisplayedUpperExpression : ℕ → ℕ → ℝ
  appliesUnderRMuchSmallerThanT : Bool
  reportedSmaller : Bool
  quantitativeSeparationSpecified : Bool
  strictComparisonEndpointScopeSpecified : Bool

noncomputable def p01NearAttainabilityEq25SmallerBoundReport :
    P01NearAttainabilitySmallerBoundReport :=
  { comparedBound := p01NearAttainabilityEq25Bound
    referenceEquation26Bound := p01NearAttainabilityEq26Bound
    referenceDisplayedUpperExpression := p01NearAttainabilityEq26UpperExpression
    appliesUnderRMuchSmallerThanT := true
    reportedSmaller := true
    quantitativeSeparationSpecified := false
    strictComparisonEndpointScopeSpecified := false }

noncomputable def p01NearAttainabilityEq28SmallerBoundReport :
    P01NearAttainabilitySmallerBoundReport :=
  { comparedBound := p01NearAttainabilityEq28Bound
    referenceEquation26Bound := p01NearAttainabilityEq26Bound
    referenceDisplayedUpperExpression := p01NearAttainabilityEq26UpperExpression
    appliesUnderRMuchSmallerThanT := true
    reportedSmaller := true
    quantitativeSeparationSpecified := false
    strictComparisonEndpointScopeSpecified := false }

/-- Computed-prefix budget for an arbitrary addition operation. -/
noncomputable def p01GenericRunningMagnitude
    (flAdd : ℝ → ℝ → ℝ) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ k : Fin n,
    if 0 < k.val then
      |p01RecursiveSum flAdd (k.val + 1) (fun i => v ⟨i.val, by omega⟩)|
    else 0

/-- Qualitative assessment of decreasing order for sums of positive numbers. -/
structure P01PositiveDecreasingLittleRecommendationReport where
  appliesToSumsOfPositiveNumbers : Bool
  concernsDecreasingAbsoluteMagnitudeOrder : Bool
  reportedToHaveLittleToRecommendIt : Bool

def p01PositiveDecreasingLittleRecommendationReport :
    P01PositiveDecreasingLittleRecommendationReport :=
  { appliesToSumsOfPositiveNumbers := true
    concernsDecreasingAbsoluteMagnitudeOrder := true
    reportedToHaveLittleToRecommendIt := true }

/-- Status-preserving form of the paper's equation-(2.8) no-smaller assertion.

The literal universal assertion is false under a permitted binary round-to-nearest model, so
it is retained as attributed source data instead of an impossible proof target.
-/
structure P01DecreasingEq28NoSmallerSourceErrorReport where
  appliesToPositiveInputs : Bool
  concernsComputedPrefixMagnitudes : Bool
  decreasingBoundAssertedNoSmaller : Bool
  literalUniversalAssertionValidInPermittedModel : Bool

def p01DecreasingEq28NoSmallerSourceErrorReport :
    P01DecreasingEq28NoSmallerSourceErrorReport :=
  { appliesToPositiveInputs := true
    concernsComputedPrefixMagnitudes := true
    decreasingBoundAssertedNoSmaller := true
    literalUniversalAssertionValidInPermittedModel := false }

/-- The separate qualitative claim that the decreasing equation-(2.8) bound can be much larger. -/
structure P01DecreasingEq28PotentiallyLargerReport where
  appliesToPositiveInputs : Bool
  concernsEquation28ComputedPrefixBound : Bool
  concernsComputedPrefixMagnitudes : Bool
  comparisonOrderingIsIncreasingMagnitude : Bool
  decreasingBoundAssertedPotentiallyMuchLarger : Bool
  quantitativeMeaningSpecified : Bool

def p01DecreasingEq28PotentiallyLargerReport :
    P01DecreasingEq28PotentiallyLargerReport :=
  { appliesToPositiveInputs := true
    concernsEquation28ComputedPrefixBound := true
    concernsComputedPrefixMagnitudes := true
    comparisonOrderingIsIncreasingMagnitude := true
    decreasingBoundAssertedPotentiallyMuchLarger := true
    quantitativeMeaningSpecified := false }

/-- The corresponding qualitative equation-(2.5) claim, whose scale is left unspecified. -/
structure P01DecreasingEq25PotentiallyLargerReport where
  appliesToPositiveInputs : Bool
  concernsEquation25WeakerBound : Bool
  comparisonOrderingIsIncreasingMagnitude : Bool
  decreasingBoundAssertedPotentiallyMuchLarger : Bool
  quantitativeMeaningSpecified : Bool

def p01DecreasingEq25PotentiallyLargerReport :
    P01DecreasingEq25PotentiallyLargerReport :=
  { appliesToPositiveInputs := true
    concernsEquation25WeakerBound := true
    comparisonOrderingIsIncreasingMagnitude := true
    decreasingBoundAssertedPotentiallyMuchLarger := true
    quantitativeMeaningSpecified := false }

/-- Possible loss of small-term contributions for widely varying positive data. -/
structure P01PositiveDecreasingSmallTermContributionReport where
  appliesToPositiveTerms : Bool
  termMagnitudesVaryWidely : Bool
  magnitudeVariationThresholdSpecified : Bool
  decreasingOrderMayPreventSmallerTermsFromContributingToTheSum : Bool

def p01PositiveDecreasingSmallTermContributionReport :
    P01PositiveDecreasingSmallTermContributionReport :=
  { appliesToPositiveTerms := true
    termMagnitudesVaryWidely := true
    magnitudeVariationThresholdSpecified := false
    decreasingOrderMayPreventSmallerTermsFromContributingToTheSum := true }

/-- Largest magnitude among all exact leaves and intermediate values. -/
noncomputable def p01MaxExactValueMagnitude (tree : P01SumTree) : ℝ :=
  tree.exactValues.map abs |>.foldl max 0

/-! ### Source explanations accompanying the section 2 and 3 comparisons -/

/-- Explanation of the exact decreasing-order result in example (2.9). -/
structure P01Eq29DecreasingExplanationReport where
  input : ℝ → Fin 4 → ℝ
  MRequiredToBeMachineBasePower : Bool
  roundingModeIsRoundToNearest : Bool
  permittedTiePolicies : List P01NearestTiePolicy
  requiresRoundOnePlusMEqualsM : Bool
  sourceInfersMStrictlyGreaterThanUnitRoundoffInverse : Bool
  concernsDecreasingOrderingInExample29 : Bool
  unitTermAddedAfterInevitableHeavyCancellation : Bool
  comparisonOrderingsAddUnitTermBeforeThatCancellation : Bool
  lateAdditionRetainsImportantInformationInUnitTerm : Bool

def p01Eq29DecreasingExplanationReport : P01Eq29DecreasingExplanationReport :=
  { input := p01Eq29Input
    MRequiredToBeMachineBasePower := true
    roundingModeIsRoundToNearest := true
    permittedTiePolicies := [.evenLastDigit, .awayFromZero]
    requiresRoundOnePlusMEqualsM := true
    sourceInfersMStrictlyGreaterThanUnitRoundoffInverse := true
    concernsDecreasingOrderingInExample29 := true
    unitTermAddedAfterInevitableHeavyCancellation := true
    comparisonOrderingsAddUnitTermBeforeThatCancellation := true
    lateAdditionRetainsImportantInformationInUnitTerm := true }

/-- Equation (2.8) is reported to predict the best ordering in example (2.9). -/
structure P01Eq29Equation28PredictionReport where
  concernsExample29 : Bool
  predictedBestOrderingIsDecreasing : Bool
  predictionComesFromEquation28BoundValues : Bool

def p01Eq29Equation28PredictionReport : P01Eq29Equation28PredictionReport :=
  { concernsExample29 := true
    predictedBestOrderingIsDecreasing := true
    predictionComesFromEquation28BoundValues := true }

/-- The equation-(2.8) prediction is described as extremely pessimistic here. -/
structure P01Eq29Equation28PessimismReport where
  concernsExample29DecreasingOrdering : Bool
  actualRoundingErrorIsZero : Bool
  equation28BoundReportedExtremelyPessimisticForThisReason : Bool

def p01Eq29Equation28PessimismReport : P01Eq29Equation28PessimismReport :=
  { concernsExample29DecreasingOrdering := true
    actualRoundingErrorIsZero := true
    equation28BoundReportedExtremelyPessimisticForThisReason := true }

/-- General weakness attributed to worst-case rounding-error bounds. -/
structure P01WorstCaseBoundCancellationLimitationReport where
  concernsWorstCaseRoundingErrorBounds : Bool
  boundsDoNotAccountForRoundingErrorsCancelling : Bool
  boundsDoNotAccountForErrorsSmallerThanWorstCaseMaxima : Bool

def p01WorstCaseBoundCancellationLimitationReport :
    P01WorstCaseBoundCancellationLimitationReport :=
  { concernsWorstCaseRoundingErrorBounds := true
    boundsDoNotAccountForRoundingErrorsCancelling := true
    boundsDoNotAccountForErrorsSmallerThanWorstCaseMaxima := true }

/-- Comparison of the general pairwise bound (3.6) with recursive bound (2.6). -/
structure P01PairwiseRecursiveGeneralBoundComparisonReport where
  comparedPairwiseEquation36WithRecursiveEquation26 : Bool
  pairwiseBoundReportedSmaller : Bool
  reasonIsLogTwoNReplacingLinearNDependence : Bool
  strictComparisonEndpointScopeSpecifiedBySource : Bool
  literalStrictComparisonHoldsAtNEqualTwo : Bool

def p01PairwiseRecursiveGeneralBoundComparisonReport :
    P01PairwiseRecursiveGeneralBoundComparisonReport :=
  { comparedPairwiseEquation36WithRecursiveEquation26 := true
    pairwiseBoundReportedSmaller := true
    reasonIsLogTwoNReplacingLinearNDependence := true
    strictComparisonEndpointScopeSpecifiedBySource := false
    literalStrictComparisonHoldsAtNEqualTwo := false }











/-- First motivation reported for the insertion strategy. -/
structure P01InsertionSimilarMagnitudeMotivationReport where
  concernsInsertionSummation : Bool
  strategyRepeatedlyUsesIncreasingOrderUntilFinalSumObtained : Bool
  motivationAttributedToReferenceNumber : ℕ
  strategyTendsToEncourageSimilarMagnitudeAdditions : Bool

def p01InsertionSimilarMagnitudeMotivationReport :
    P01InsertionSimilarMagnitudeMotivationReport :=
  { concernsInsertionSummation := true
    strategyRepeatedlyUsesIncreasingOrderUntilFinalSumObtained := true
    motivationAttributedToReferenceNumber := 35
    strategyTendsToEncourageSimilarMagnitudeAdditions := true }

/-- Information-retention comparison used to motivate similar-magnitude additions. -/
structure P01SimilarMagnitudeInformationRetentionReport where
  similarMagnitudeAdditionsReportedPreferred : Bool
  preferenceJustifiedByRetainingMoreAddendInformation : Bool
  similarMagnitudeAdditionsReportedToRetainMoreAddendInformation : Bool
  largePlusSmallCanLoseManySignificantDigitsFromSmallAddend : Bool

def p01SimilarMagnitudeInformationRetentionReport :
    P01SimilarMagnitudeInformationRetentionReport :=
  { similarMagnitudeAdditionsReportedPreferred := true
    preferenceJustifiedByRetainingMoreAddendInformation := true
    similarMagnitudeAdditionsReportedToRetainMoreAddendInformation := true
    largePlusSmallCanLoseManySignificantDigitsFromSmallAddend := true }

/-- Sequential objective attributed to the insertion strategy in equation (3.3). -/
structure P01InsertionSequentialInternalMagnitudeObjectiveReport where
  concernsInsertionSummation : Bool
  targetTermsAreHattedTermsInErrorExpression33 : Bool
  targetTermsRunFromTHatSubNPlusOneThroughTHatSubTwoNMinusOne : Bool
  absoluteValuesMinimizedOneAtATime : Bool

def p01InsertionSequentialInternalMagnitudeObjectiveReport :
    P01InsertionSequentialInternalMagnitudeObjectiveReport :=
  { concernsInsertionSummation := true
    targetTermsAreHattedTermsInErrorExpression33 := true
    targetTermsRunFromTHatSubNPlusOneThroughTHatSubTwoNMinusOne := true
    absoluteValuesMinimizedOneAtATime := true }

/-- Heavy-cancellation tendency stated after the plus/minus maximum claim. -/
structure P01PlusMinusHeavyCancellationInternalMagnitudeReport where
  scope : P01HeavyCancellationScopeReport
  concernsMaximumAbsoluteInternalValue : Bool
  plusMinusValueTendsToBeMuchLargerThanForOtherConsideredMethods : Bool

noncomputable def p01PlusMinusHeavyCancellationInternalMagnitudeReport :
    P01PlusMinusHeavyCancellationInternalMagnitudeReport :=
  { scope := p01HeavyCancellationScopeReport
    concernsMaximumAbsoluteInternalValue := true
    plusMinusValueTendsToBeMuchLargerThanForOtherConsideredMethods := true }

/-- Overall qualitative assessment of plus/minus summation before the final method. -/
structure P01PlusMinusNoAdvantagesAssessmentReport where
  comparisonClassIsOtherMethodsConsideredHere : Bool
  plusMinusReportedToHaveNoAdvantagesOverThoseMethods : Bool

def p01PlusMinusNoAdvantagesAssessmentReport :
    P01PlusMinusNoAdvantagesAssessmentReport :=
  { comparisonClassIsOtherMethodsConsideredHere := true
    plusMinusReportedToHaveNoAdvantagesOverThoseMethods := true }

/-- The stated arithmetic limitation of Gill's rounding-error estimate. -/
structure P01GillFixedPointEstimateLimitationReport where
  concernsGillsEstimate : Bool
  estimateReportedValidForFixedPointArithmeticOnly : Bool

def p01GillFixedPointEstimateLimitationReport :
    P01GillFixedPointEstimateLimitationReport :=
  { concernsGillsEstimate := true
    estimateReportedValidForFixedPointArithmeticOnly := true }

/-- Kahan's and Møller's historical extension of Gill's idea. -/
structure P01KahanMollerFloatingPointExtensionReport where
  kahanExtendedGillsRoundingErrorEstimationIdea : Bool
  mollerExtendedGillsRoundingErrorEstimationIdea : Bool
  extensionsApplyToFloatingPointArithmetic : Bool

def p01KahanMollerFloatingPointExtensionReport :
    P01KahanMollerFloatingPointExtensionReport :=
  { kahanExtendedGillsRoundingErrorEstimationIdea := true
    mollerExtendedGillsRoundingErrorEstimationIdea := true
    extensionsApplyToFloatingPointArithmetic := true }

/-- Møller's version estimates the addition error in chopped arithmetic. -/
structure P01MollerChoppedArithmeticEstimateReport where
  mollerShowsHowToEstimateTheQuantity : Bool
  estimatedQuantity : (ℝ → ℝ) → ℝ → ℝ → ℝ
  estimatedQuantityIsExactSumMinusRoundedSum : Bool
  arithmeticModeIsChopping : Bool

def p01MollerChoppedArithmeticEstimateReport :
    P01MollerChoppedArithmeticEstimateReport :=
  { mollerShowsHowToEstimateTheQuantity := true
    estimatedQuantity := fun fl a b => a + b - fl (a + b)
    estimatedQuantityIsExactSumMinusRoundedSum := true
    arithmeticModeIsChopping := true }

/-- Comparative description of Kahan's rounding-error estimate. -/
structure P01KahanSimplerEstimateReport where
  comparisonReferenceIsMollersEstimate : Bool
  kahanEstimateReportedSlightlySimpler : Bool

def p01KahanSimplerEstimateReport : P01KahanSimplerEstimateReport :=
  { comparisonReferenceIsMollersEstimate := true
    kahanEstimateReportedSlightlySimpler := true }

/-- Use of Kahan's estimate to derive compensated summation. -/
structure P01KahanCompensatedSummationDerivationReport where
  mollerEstimateIsExactSumMinusRoundedSumInChoppedArithmetic : Bool
  kahanEstimateReportedSlightlySimplerThanMollers : Bool
  usesKahansRoundingErrorEstimate : Bool
  derivationUsesThatEstimate : Bool
  derivesCompensatedSummationForFiniteSums : Bool

def p01KahanCompensatedSummationDerivationReport :
    P01KahanCompensatedSummationDerivationReport :=
  { mollerEstimateIsExactSumMinusRoundedSumInChoppedArithmetic := true
    kahanEstimateReportedSlightlySimplerThanMollers := true
    usesKahansRoundingErrorEstimate := true
    derivationUsesThatEstimate := true
    derivesCompensatedSummationForFiniteSums := true }

/-- Algorithmic idea behind compensated summation. -/
structure P01CompensatedRoundingFeedbackIdeaReport where
  concernsCompensatedSummation : Bool
  capturesRoundingErrors : Bool
  feedsCapturedErrorsBackIntoSummation : Bool

def p01CompensatedRoundingFeedbackIdeaReport :
    P01CompensatedRoundingFeedbackIdeaReport :=
  { concernsCompensatedSummation := true
    capturesRoundingErrors := true
    feedsCapturedErrorsBackIntoSummation := true }

/-- Qualitative assessment of backward-error result (3.10). -/
structure P01Equation310BackwardErrorAssessmentReport where
  concernsEquation310 : Bool
  describedAsAlmostIdealBackwardErrorResult : Bool

def p01Equation310BackwardErrorAssessmentReport :
    P01Equation310BackwardErrorAssessmentReport :=
  { concernsEquation310 := true
    describedAsAlmostIdealBackwardErrorResult := true }

/-- Effect of the stronger final-corrected bound on the comparison with (2.3). -/
structure P01FinalCorrectionDimensionDependenceReport where
  governingBackwardClaim : P01StandardAddFamily → Prop
  governingBackwardClaim_eq :
    governingBackwardClaim = P01FinalCorrectedBackwardRepresentationClaim
  equation310WithThisBoundReportedEssentiallyEquation23 : Bool
  dimensionDependenceTransferredFromLinearRoundoffTermToQuadraticTerm : Bool

def p01FinalCorrectionDimensionDependenceReport :
    P01FinalCorrectionDimensionDependenceReport :=
  { governingBackwardClaim := P01FinalCorrectedBackwardRepresentationClaim
    governingBackwardClaim_eq := rfl
    equation310WithThisBoundReportedEssentiallyEquation23 := true
    dimensionDependenceTransferredFromLinearRoundoffTermToQuadraticTerm := true }

/-- Forward-error comparison stated for equation (3.11). -/
structure P01Equation311ImprovementReport where
  appliesWhenNUnitRoundoffAtMostOne : Bool
  constantInEquation311BoundAssertedIndependentOfN : Bool
  significantlyImprovesOnRecursiveEquation26 : Bool
  significantlyImprovesOnPairwiseEquation36 : Bool

def p01Equation311ImprovementReport : P01Equation311ImprovementReport :=
  { appliesWhenNUnitRoundoffAtMostOne := true
    constantInEquation311BoundAssertedIndependentOfN := true
    significantlyImprovesOnRecursiveEquation26 := true
    significantlyImprovesOnPairwiseEquation36 := true }

/-- Precise qualitative weakness of (3.12) relative to (3.10). -/
structure P01Equation312SecondOrderWeaknessReport where
  comparesEquation312WithEquation310 : Bool
  secondOrderTermHasOneExtraFactorN : Bool
  equation312ReportedWeakerForThatReason : Bool

def p01Equation312SecondOrderWeaknessReport :
    P01Equation312SecondOrderWeaknessReport :=
  { comparesEquation312WithEquation310 := true
    secondOrderTermHasOneExtraFactorN := true
    equation312ReportedWeakerForThatReason := true }

/-! ### Remaining no-guard consequences -/

/-- Positive unit-roundoff values, used for genuine one-sided asymptotics. -/
abbrev P01PositiveRoundoff := {u : ℝ // 0 < u}

/-- A no-guard model family parametrized by its exact unit roundoff. -/
structure P01NoGuardFamily where
  model : P01PositiveRoundoff → NoGuardAddModel
  roundoff_eq : ∀ u, (model u).u = (u : ℝ)

/-- Arithmetic outcome of the cited Cray subtraction example. -/
structure P01CraySubtractionOutcomeReport where
  appliesToCrayComputers : Bool
  appliesToEveryPowerOfTwo : Bool
  subtractsPowerOfTwoFromNextSmallerFloatingPointNumber : Bool
  resultCanBeZero : Bool
  resultCanBeTwiceTheExactDifference : Bool

def p01CraySubtractionOutcomeReport : P01CraySubtractionOutcomeReport :=
  { appliesToCrayComputers := true
    appliesToEveryPowerOfTwo := true
    subtractsPowerOfTwoFromNextSmallerFloatingPointNumber := true
    resultCanBeZero := true
    resultCanBeTwiceTheExactDifference := true }

/-- Perturbation size forced by that outcome in the standard relative model. -/
structure P01CrayRequiredRelativePerturbationReport where
  concernsStandardRelativeErrorExpressionForCitedSubtraction : Bool
  expressionCanBeRepresentedWithPerturbationMagnitudeAtMostOne : Bool
  unitRoundoffSizedPerturbationDoesNotSuffice : Bool
  requiredPerturbationMagnitude : ℚ
  citationReference : ℕ

def p01CrayRequiredRelativePerturbationReport :
    P01CrayRequiredRelativePerturbationReport :=
  { concernsStandardRelativeErrorExpressionForCitedSubtraction := true
    expressionCanBeRepresentedWithPerturbationMagnitudeAtMostOne := true
    unitRoundoffSizedPerturbationDoesNotSuffice := true
    requiredPerturbationMagnitude := 1
    citationReference := 20 }

/-- Scope of the source's model-(1.2) invalidation statement. -/
structure P01CrayStandardModelInvalidationReport where
  paperErrorAnalysisIsBasedOnEquation12 : Bool
  concernsStandardRelativeArithmeticModelEquation12 : Bool
  modelInvalidOnMachinesThatLackAdditionGuardDigit : Bool
  crayComputersReportedAsNotableExamples : Bool

def p01CrayStandardModelInvalidationReport :
    P01CrayStandardModelInvalidationReport :=
  { paperErrorAnalysisIsBasedOnEquation12 := true
    concernsStandardRelativeArithmeticModelEquation12 := true
    modelInvalidOnMachinesThatLackAdditionGuardDigit := true
    crayComputersReportedAsNotableExamples := true }

/-- Equation (3.10) does not hold universally in the no-guard model. -/
structure P01NoGuardEquation310FailureReport where
  appliesToNoGuardArithmeticModel : Bool
  compensatedBackwardResultEquation310Universal : Bool

def p01NoGuardEquation310FailureReport :
    P01NoGuardEquation310FailureReport :=
  { appliesToNoGuardArithmeticModel := true
    compensatedBackwardResultEquation310Universal := false }

/-- Kahan is reported to construct a Cray counterexample to equation (3.11). -/
structure P01CrayEquation311CounterexampleReport where
  exampleAttributedToKahan : Bool
  citationReference : ℕ
  concernsCompensatedSummation : Bool
  appliesToCrayNoGuardArithmetic : Bool
  constructedExampleViolatesEquation311 : Bool

def p01CrayEquation311CounterexampleReport :
    P01CrayEquation311CounterexampleReport :=
  { exampleAttributedToKahan := true
    citationReference := 20
    concernsCompensatedSummation := true
    appliesToCrayNoGuardArithmetic := true
    constructedExampleViolatesEquation311 := true }

/-- Kahan separately reports that the Cray failure of (3.11) is extremely rare. -/
structure P01CrayEquation311FailureRarityReport where
  rarityStatementAttributedToKahan : Bool
  concernsCrayCompensatedSummationFailure : Bool
  failureReportedExtremelyRare : Bool

def p01CrayEquation311FailureRarityReport :
    P01CrayEquation311FailureRarityReport :=
  { rarityStatementAttributedToKahan := true
    concernsCrayCompensatedSummationFailure := true
    failureReportedExtremelyRare := true }

/-- Reported hardware-domain success of the modified compensated algorithm. -/
structure P01NoGuardModifiedHardwareSuccessReport where
  concernsModifiedCompensatedAlgorithm : Bool
  hardwareDomainDescribedAsAllNorthAmericanMachinesWithFloatingHardware : Bool
  achievesEquation310OnThatReportedDomain : Bool

def p01NoGuardModifiedHardwareSuccessReport :
    P01NoGuardModifiedHardwareSuccessReport :=
  { concernsModifiedCompensatedAlgorithm := true
    hardwareDomainDescribedAsAllNorthAmericanMachinesWithFloatingHardware := true
    achievesEquation310OnThatReportedDomain := true }

/-- The printed constant and the explicitly tentative replacement interval. -/
structure P01NoGuardModifiedConstantRangeReport where
  printedConstant : ℚ
  suggestedReplacementLower : ℚ
  suggestedReplacementUpper : ℚ
  endpointInclusivitySpecifiedBySource : Bool
  replacementRangeIsTentative : Bool

def p01NoGuardModifiedConstantRangeReport :
    P01NoGuardModifiedConstantRangeReport :=
  { printedConstant := 23 / 50
    suggestedReplacementLower := 1 / 4
    suggestedReplacementUpper := 1 / 2
    endpointInclusivitySpecifiedBySource := false
    replacementRangeIsTentative := true }

/-- Qualitative adjective applied to the printed modified-algorithm constant. -/
structure P01NoGuardModifiedConstantCharacterizationReport where
  characterizedConstant : ℚ
  constantCalledMysterious : Bool

def p01NoGuardModifiedConstantCharacterizationReport :
    P01NoGuardModifiedConstantCharacterizationReport :=
  { characterizedConstant := 23 / 50
    constantCalledMysterious := true }

/-- The proof of the modified algorithm is reported to inspect known machine designs. -/
structure P01NoGuardModifiedProofDependenceReport where
  concernsProofOfModifiedAlgorithmGuarantee : Bool
  proofRequiresConsiderationOfKnownMachineDesigns : Bool

def p01NoGuardModifiedProofDependenceReport :
    P01NoGuardModifiedProofDependenceReport :=
  { concernsProofOfModifiedAlgorithmGuarantee := true
    proofRequiresConsiderationOfKnownMachineDesigns := true }

/-! ### Experiment specifications and reported mathematical conclusions -/

/-- Positive-input identity reported for the three named orderings/methods. -/
structure P01PositivePsumPlusMinusIncreasingIdentityReport where
  appliesToPositiveInputs : Bool
  psumPlusMinusAndIncreasingReportedIdentical : Bool
  orderingTieBreakingSpecifiedBySource : Bool

def p01PositivePsumPlusMinusIncreasingIdentityReport :
    P01PositivePsumPlusMinusIncreasingIdentityReport :=
  { appliesToPositiveInputs := true
    psumPlusMinusAndIncreasingReportedIdentical := true
    orderingTieBreakingSpecifiedBySource := false }

/-- Status-aware literal positive-input bound sentence preceding Table 6.3. -/
structure P01PositiveInputBoundSourceIssueReport where
  appliesToStrictlyPositiveInputs : Bool
  methods : List P01SummationMethod
  relativeErrorReportedAtMostMethodCoefficientTimesUnitRoundoff : Bool
  coefficientDependsOnMethod : Bool
  coefficientReportedAtMostN : Bool
  sentenceExplicitlyQualifiedAsFirstOrder : Bool
  literalExactValiditySupportedByEarlierBounds : Bool

def p01PositiveInputBoundSourceIssueReport :
    P01PositiveInputBoundSourceIssueReport :=
  { appliesToStrictlyPositiveInputs := true
    methods := p01EightSummationMethods
    relativeErrorReportedAtMostMethodCoefficientTimesUnitRoundoff := true
    coefficientDependsOnMethod := true
    coefficientReportedAtMostN := true
    sentenceExplicitlyQualifiedAsFirstOrder := false
    literalExactValiditySupportedByEarlierBounds := false }

/-- Construction and intended role of the a-priori experiment reference sum. -/
structure P01ReferenceSumConstructionReport where
  inputsAreSinglePrecisionNumbers : Bool
  usesRecursiveSummation : Bool
  arithmeticIsDoublePrecision : Bool
  constructedValueIsAnApproximationToExactSumSn : Bool

def p01ReferenceSumConstructionReport : P01ReferenceSumConstructionReport :=
  { inputsAreSinglePrecisionNumbers := true
    usesRecursiveSummation := true
    arithmeticIsDoublePrecision := true
    constructedValueIsAnApproximationToExactSumSn := true }

/-- Empirical status and exact formula of the strict reference-sum
certification criterion. -/
structure P01ReferenceSumCriterionObservedReport where
  concernsAprioriExperimentReferenceSums : Bool
  strictCriterion :
    (doubleUnitRoundoff singleUnitRoundoff : ℝ) →
      (n : ℕ) → (Fin n → ℝ) → Prop
  strictCriterion_eq :
    strictCriterion = fun (doubleUnitRoundoff singleUnitRoundoff : ℝ)
        (n : ℕ) (v : Fin n → ℝ) =>
      (n : ℝ) * doubleUnitRoundoff * p01AbsoluteSum n v <
        singleUnitRoundoff * |p01ExactSum n v|
  strictCertificationCriterionHeldInEveryTest : Bool

def p01ReferenceSumCriterionObservedReport :
    P01ReferenceSumCriterionObservedReport :=
  { concernsAprioriExperimentReferenceSums := true
    strictCriterion := fun (doubleUnitRoundoff singleUnitRoundoff : ℝ)
        (n : ℕ) (v : Fin n → ℝ) =>
      (n : ℝ) * doubleUnitRoundoff * p01AbsoluteSum n v <
        singleUnitRoundoff * |p01ExactSum n v|
    strictCriterion_eq := rfl
    strictCertificationCriterionHeldInEveryTest := true }

/-- The paper says equation (2.6) supplies the reference-sum certification. -/
structure P01ReferenceSumEquation26CertificationReport where
  concernsSinglePrecisionAccuracyOfDoubleReferenceSum : Bool
  certificationInvokesEquation26 : Bool

def p01ReferenceSumEquation26CertificationReport :
    P01ReferenceSumEquation26CertificationReport :=
  { concernsSinglePrecisionAccuracyOfDoubleReferenceSum := true
    certificationInvokesEquation26 := true }

/-- Real MDS proposals converted to the simulated-single data actually summed. -/
noncomputable def p01SimulatedSingleData
    (fp : P01BinaryRoundModel) {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.round (v i)

/-- Single-precision specialization of the neutral eight-method semantics. -/
def P01ExperimentMethodEvaluation
    (fp : P01BinaryRoundModel) (method : P01SummationMethod)
    {n : ℕ} (v : Fin n → ℝ) (result : ℝ) : Prop :=
  fp.precision = 23 ∧
    (∀ i, P01BaseTwoRepresentable fp.precision (v i)) ∧
    P01SummationMethodEvaluation (p01RoundAdd fp) method v result

/-- Standard-addition specialization of the neutral eight-method semantics. -/
def P01StandardMethodEvaluation
    (fp : P01StandardAddModel) (method : P01SummationMethod)
    {n : ℕ} (v : Fin n → ℝ) (result : ℝ) : Prop :=
  P01SummationMethodEvaluation fp.fl_add method v result

/-- The paper's first-order equation-(2.6) assertion for every one of the
eight examined summation methods.  The assertion is retained as a
source-facing family: its `C` and sufficiently small positive threshold may
depend on the method and on the input length, but not on the inputs or result
chosen below that threshold. -/
def P01AllExaminedMethodsEquation26Claim
    (family : P01StandardAddFamily) : Prop :=
  ∀ method : P01SummationMethod, method ∈ p01EightSummationMethods →
    ∀ n : ℕ, 0 < n →
      ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
        ∀ u : NNReal, 0 < (u : ℝ) → (u : ℝ) ≤ ε →
          ∀ (v : Fin n → ℝ) (result : ℝ),
            P01InputsRepresentableForAdd (family.model u) n v →
            P01StandardMethodEvaluation (family.model u) method v result →
            |result - p01ExactSum n v| ≤
              (((n - 1 : ℕ) : ℝ) * (u : ℝ) + C * (u : ℝ) ^ 2) *
                p01AbsoluteSum n v

/-- The paper's equation-(2.6) first-order error claim for all eight examined
methods. This source-facing proposition records the quantified claim without
turning its asymptotic wording into an additional proof obligation. -/
def p01_t4_all_examined_methods_equation26
    (family : P01StandardAddFamily) : Prop :=
  P01AllExaminedMethodsEquation26Claim family

/-- A function-value-only maximization problem tied to a selected summation semantics. -/
structure P01MaximizationProblem where
  dimension : ℕ
  fp : P01BinaryRoundModel
  singlePrecision : fp.precision = 23
  method : P01SummationMethod
  usesMatlabImplementation : Bool
  matlabImplementationReferenceNumber : ℕ
  searchMethodName : String
  searchMethodReferenceNumbers : List ℕ
  attemptsToLocateMaximizer : Bool
  usesFunctionValuesOnly : Bool
  objectiveIsRelativeErrorOfComputedSum : Bool
  paperInitiallyAppliesProtocolToIncreasingRecursiveSummation : Bool

/-- Legal result relation for the selected single-precision summation method. -/
def P01MaximizationProblem.FeasibleResult
    (problem : P01MaximizationProblem)
    (v : Fin problem.dimension → ℝ) (result : ℝ) : Prop :=
  let data := p01SimulatedSingleData problem.fp v
  p01ExactSum problem.dimension data ≠ 0 ∧
    P01ExperimentMethodEvaluation problem.fp problem.method data result

/-- Relative summation error maximized by MDS over legal input/result pairs. -/
noncomputable def P01MaximizationProblem.objective
    (problem : P01MaximizationProblem)
    (v : Fin problem.dimension → ℝ) (result : ℝ) : ℝ :=
  p01ReportedRelativeError result
    (p01ExactSum problem.dimension (p01SimulatedSingleData problem.fp v))

/-- A feasible input/result pair solves the stated problem when its reported
relative error is at least that of every other feasible pair. -/
def P01MaximizationProblem.IsMaximizer
    (problem : P01MaximizationProblem)
    (v : Fin problem.dimension → ℝ) (result : ℝ) : Prop :=
  problem.FeasibleResult v result ∧
    ∀ w : Fin problem.dimension → ℝ, ∀ other : ℝ,
      problem.FeasibleResult w other →
        problem.objective w other ≤ problem.objective v result

/-- The paper's MDS problem for any one of its eight simulated-single methods. -/
def p01MDSMaximizationProblem
    (fp : P01BinaryRoundModel) (hprecision : fp.precision = 23)
    (n : ℕ) (method : P01SummationMethod) : P01MaximizationProblem :=
  { dimension := n
    fp := fp
    singlePrecision := hprecision
    method := method
    usesMatlabImplementation := true
    matlabImplementationReferenceNumber := 12
    searchMethodName := "multidirectional search (MDS)"
    searchMethodReferenceNumbers := [39, 40]
    attemptsToLocateMaximizer := true
    usesFunctionValuesOnly := true
    objectiveIsRelativeErrorOfComputedSum := true
    paperInitiallyAppliesProtocolToIncreasingRecursiveSummation := true }

/-- Shared scope of the reciprocal MDS error-ratio searches on page 796. -/
structure P01MDSRatioComparisonScope where
  dimension : ℕ
  firstMethod : P01SummationMethod
  secondMethod : P01SummationMethod

def p01MDSRatioComparisonScope : P01MDSRatioComparisonScope :=
  { dimension := 3
    firstMethod := .increasing
    secondMethod := .compensated }

/-- The increasing-over-compensated error ratio was made arbitrarily large. -/
structure P01MDSFirstOverSecondRatioReport where
  scope : P01MDSRatioComparisonScope
  comparisonUsesMDSMaximizer : Bool
  certainStartingValuesRequired : Bool
  ratioObservedArbitrarilyLarge : Bool

def p01MDSFirstOverSecondRatioReport : P01MDSFirstOverSecondRatioReport :=
  { scope := p01MDSRatioComparisonScope
    comparisonUsesMDSMaximizer := true
    certainStartingValuesRequired := true
    ratioObservedArbitrarilyLarge := true }

/-- The reciprocal compensated-over-increasing error ratio was made arbitrarily large. -/
structure P01MDSSecondOverFirstRatioReport where
  scope : P01MDSRatioComparisonScope
  comparisonUsesMDSMaximizer : Bool
  certainStartingValuesRequired : Bool
  ratioObservedArbitrarilyLarge : Bool

def p01MDSSecondOverFirstRatioReport : P01MDSSecondOverFirstRatioReport :=
  { scope := p01MDSRatioComparisonScope
    comparisonUsesMDSMaximizer := true
    certainStartingValuesRequired := true
    ratioObservedArbitrarilyLarge := true }

/-- Reported mechanism for the two arbitrarily large reciprocal ratios. -/
structure P01MDSZeroDenominatorMechanismReport where
  scope : P01MDSRatioComparisonScope
  maximizerConvergedToDataWithZeroDenominatorError : Bool

def p01MDSZeroDenominatorMechanismReport :
    P01MDSZeroDenominatorMechanismReport :=
  { scope := p01MDSRatioComparisonScope
    maximizerConvergedToDataWithZeroDenominatorError := true }

/-- Similar ratio behavior was observed for method pairs outside the named pair. -/
structure P01MDSOtherMethodPairsBehaviorReport where
  namedComparisonScope : P01MDSRatioComparisonScope
  sameMDSMaximizerAndErrorRatioProtocol : Bool
  similarBehaviorMeansArbitrarilyLargeRatiosFromZeroDenominatorError : Bool
  similarBehaviorObservedForOtherMethodPairs : Bool

def p01MDSOtherMethodPairsBehaviorReport :
    P01MDSOtherMethodPairsBehaviorReport :=
  { namedComparisonScope := p01MDSRatioComparisonScope
    sameMDSMaximizerAndErrorRatioProtocol := true
    similarBehaviorMeansArbitrarilyLargeRatiosFromZeroDenominatorError := true
    similarBehaviorObservedForOtherMethodPairs := true }

/-- A data-independent relative error bound for a possibly relational summation method. -/
def P01UniformRelativeErrorBound {n : ℕ}
    (u : ℝ) (evaluation : (Fin n → ℝ) → ℝ → Prop) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (v : Fin n → ℝ) (result : ℝ),
    evaluation v result →
      |result - p01ExactSum n v| ≤ c * u * |p01ExactSum n v|

/-- Compensated summation after arranging the input in decreasing magnitude. -/
def P01DecreasingCompensatedEvaluation
    (fp : P01BinaryRoundModel) {n : ℕ}
    (v : Fin n → ℝ) (result : ℝ) : Prop :=
  (∀ i, P01BaseTwoRepresentable fp.precision (v i)) ∧
  ∃ p : Equiv.Perm (Fin n),
    P01DecreasingMagnitude v p ∧
    result = p01CompensatedSum (p01RoundAdd fp) (List.ofFn (p01Permuted v p))

/-- Every tried decreasing-compensated problem had relative error at most single roundoff. -/
structure P01DecreasingCompensatedTriedErrorReport where
  concernsDecreasingMagnitudeCompensatedSummation : Bool
  allTriedRelativeErrorsAtMostSingleRoundoff : Bool

def p01DecreasingCompensatedTriedErrorReport :
    P01DecreasingCompensatedTriedErrorReport :=
  { concernsDecreasingMagnitudeCompensatedSummation := true
    allTriedRelativeErrorsAtMostSingleRoundoff := true }

/-- The MDS search did not find a decreasing-compensated error above single roundoff. -/
structure P01DecreasingCompensatedMDSSearchReport where
  concernsDecreasingMagnitudeCompensatedSummation : Bool
  searchTargetWasRelativeErrorAboveSingleRoundoff : Bool
  maximizerFoundTarget : Bool

def p01DecreasingCompensatedMDSSearchReport :
    P01DecreasingCompensatedMDSSearchReport :=
  { concernsDecreasingMagnitudeCompensatedSummation := true
    searchTargetWasRelativeErrorAboveSingleRoundoff := true
    maximizerFoundTarget := false }

/-- Nonzero three-term relative-bound assessment stated as an appearance. -/
structure P01DecreasingCompensatedNonzeroBoundAssessmentReport where
  concernsDecreasingMagnitudeCompensatedSummation : Bool
  dimension : ℕ
  requiresNonzeroExactSum : Bool
  dataIndependentRelativeBoundAppearsImpossible : Bool

def p01DecreasingCompensatedNonzeroBoundAssessmentReport :
    P01DecreasingCompensatedNonzeroBoundAssessmentReport :=
  { concernsDecreasingMagnitudeCompensatedSummation := true
    dimension := 3
    requiresNonzeroExactSum := true
    dataIndependentRelativeBoundAppearsImpossible := true }

/-- Separate practical assessment based only on the authors limited experience. -/
structure P01DecreasingCompensatedPracticalPerformanceReport where
  concernsDecreasingMagnitudeCompensatedSummation : Bool
  evidenceExplicitlyLimitedToAuthorsExperience : Bool
  experienceSuggestsRemarkablyGoodPracticalPerformance : Bool

def p01DecreasingCompensatedPracticalPerformanceReport :
    P01DecreasingCompensatedPracticalPerformanceReport :=
  { concernsDecreasingMagnitudeCompensatedSummation := true
    evidenceExplicitlyLimitedToAuthorsExperience := true
    experienceSuggestsRemarkablyGoodPracticalPerformance := true }

/-- Open status of the request to explain the reported practical performance. -/
structure P01DecreasingCompensatedExplanationOpenQuestionReport where
  concernsReasonForRemarkablyGoodPracticalPerformance : Bool
  posedAsInterestingToDetermine : Bool
  explanationProvidedByPaper : Bool

def p01DecreasingCompensatedExplanationOpenQuestionReport :
    P01DecreasingCompensatedExplanationOpenQuestionReport :=
  { concernsReasonForRemarkablyGoodPracticalPerformance := true
    posedAsInterestingToDetermine := true
    explanationProvidedByPaper := false }

/-- Extent assessment introducing the cited body of further experiments. -/
structure P01PriorExperimentLiteratureExtentReport where
  furtherTestResultsExistInLiterature : Bool
  anyReportedFurtherTestsAreExtensive : Bool

def p01PriorExperimentLiteratureExtentReport :
    P01PriorExperimentLiteratureExtentReport :=
  { furtherTestResultsExistInLiterature := true
    anyReportedFurtherTestsAreExtensive := false }

/-- Parameters of the externally cited Linz experiment. -/
structure P01LinzExperimentReport where
  inputDistributionUniformZeroOne : Bool
  inputCount : ℕ
  trialCount : ℕ
  errorsAveragedAcrossTrials : Bool
  comparedRecursiveAndPairwiseSummation : Bool

def p01LinzExperimentReport : P01LinzExperimentReport :=
  { inputDistributionUniformZeroOne := true
    inputCount := 2048
    trialCount := 20
    errorsAveragedAcrossTrials := true
    comparedRecursiveAndPairwiseSummation := true }

/-- Caprani is reported to run a Linz-like test that also includes compensation. -/
structure P01CapraniExperimentReport where
  citedReferenceNumber : ℕ
  experimentReportedSimilarToLinz : Bool
  compensatedSummationIncluded : Bool

def p01CapraniExperimentReport : P01CapraniExperimentReport :=
  { citedReferenceNumber := 4
    experimentReportedSimilarToLinz := true
    compensatedSummationIncluded := true }

/-- Gregory is separately reported to run a Linz-like test including compensation. -/
structure P01GregoryExperimentReport where
  citedReferenceNumber : ℕ
  experimentReportedSimilarToLinz : Bool
  compensatedSummationIncluded : Bool

def p01GregoryExperimentReport : P01GregoryExperimentReport :=
  { citedReferenceNumber := 10
    experimentReportedSimilarToLinz := true
    compensatedSummationIncluded := true }

/-- Problems and methods in the externally cited Linnainmaa experiments. -/
structure P01LinnainmaaExperimentReport where
  comparedRecursiveAndCompensatedSummation : Bool
  appliedToSeriesExpansions : Bool
  appliedToSimpsonsRuleForQuadrature : Bool
  appliedToGillsRungeKuttaMethod : Bool

def p01LinnainmaaExperimentReport : P01LinnainmaaExperimentReport :=
  { comparedRecursiveAndCompensatedSummation := true
    appliedToSeriesExpansions := true
    appliedToSimpsonsRuleForQuadrature := true
    appliedToGillsRungeKuttaMethod := true }

/-- Scope of the externally cited Robertazzi--Schwartz experiments. -/
structure P01RobertazziSchwartzExperimentReport where
  evaluatedAverageMeanSquareErrors : Bool
  comparedRecursiveIncreasingDecreasingAndRandomOrderings : Bool
  comparedPairwiseSummation : Bool
  comparedInsertionSummation : Bool
  usedUniformZeroOneDistribution : Bool
  usedExponentialDistribution : Bool
  exponentialMean : ℚ
  inclusiveInputLimit : ℕ

def p01RobertazziSchwartzExperimentReport :
    P01RobertazziSchwartzExperimentReport :=
  { evaluatedAverageMeanSquareErrors := true
    comparedRecursiveIncreasingDecreasingAndRandomOrderings := true
    comparedPairwiseSummation := true
    comparedInsertionSummation := true
    usedUniformZeroOneDistribution := true
    usedExponentialDistribution := true
    exponentialMean := 1 / 2
    inclusiveInputLimit := 4096 }

/-- A summation functional whose answer is independent of the input permutation. -/
def P01PermutationInvariant
    (method : (n : ℕ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ) (p : Equiv.Perm (Fin n)),
    method n (p01Permuted v p) = method n v

/-- Increasing magnitude order with equal magnitudes ordered by numerical sign. -/
def P01IncreasingSignOrdered (xs : List ℝ) : Prop :=
  xs.Pairwise fun x y => |x| < |y| ∨ (|x| = |y| ∧ x ≤ y)

/-- Pair contributions to the extended Rosenbrock function. -/
noncomputable def p01RosenbrockTerms
    (m : ℕ) (x : Fin (2 * m) → ℝ) : Fin m → ℝ :=
  fun i =>
    100 * (x (p01RosenbrockRightIndex m i) -
      x (p01RosenbrockLeftIndex m i) ^ 2) ^ 2 +
    (1 - x (p01RosenbrockLeftIndex m i)) ^ 2

/-! ### Algorithms and summary claims not attached to numbered equations -/

/-- Numerical and optimizer setup of the cited sonar-array application. -/
structure P01SonarApplicationSetupReport where
  citedAuthors : String
  citedReferenceNumber : ℕ
  quotedStatementPageInCitedReference : ℕ
  citedAuthorsDerivedOptimizationAlgorithm : Bool
  optimizationProblemArisesInSonarArrayDesign : Bool
  quotedGradientStatementAttributedToCitedAuthors : Bool
  objectiveGradientIsTheGradientInCitedEquation41 : Bool
  objectiveGradientIsSumOfMTerms : Bool
  reportedM : ℕ
  reportedN : ℕ
  optimizerName : String

def p01SonarApplicationSetupReport : P01SonarApplicationSetupReport :=
  { citedAuthors := "Lasdon et al."
    citedReferenceNumber := 24
    quotedStatementPageInCitedReference := 145
    citedAuthorsDerivedOptimizationAlgorithm := true
    optimizationProblemArisesInSonarArrayDesign := true
    quotedGradientStatementAttributedToCitedAuthors := true
    objectiveGradientIsTheGradientInCitedEquation41 := true
    objectiveGradientIsSumOfMTerms := true
    reportedM := 284
    reportedN := 42
    optimizerName := "GRG2" }

/-- Occurrence of optimizer difficulties in the cited sonar setup. -/
structure P01SonarOptimizerDifficultiesReport where
  citedOptimizerName : String
  occurrenceAttributedToCitedAuthors : Bool
  optimizerEncounteredDifficulties : Bool

def p01SonarOptimizerDifficultiesReport :
    P01SonarOptimizerDifficultiesReport :=
  { citedOptimizerName := "GRG2"
    occurrenceAttributedToCitedAuthors := true
    optimizerEncounteredDifficulties := true }

/-- Separately reported cause of those optimizer difficulties. -/
structure P01SonarInaccurateGradientCauseReport where
  citedOptimizerName : String
  optimizerEncounteredDifficulties : Bool
  causalClaimAttributedToCitedAuthors : Bool
  difficultiesStemmedFromInaccurateGradientEvaluation : Bool

def p01SonarInaccurateGradientCauseReport :
    P01SonarInaccurateGradientCauseReport :=
  { citedOptimizerName := "GRG2"
    optimizerEncounteredDifficulties := true
    causalClaimAttributedToCitedAuthors := true
    difficultiesStemmedFromInaccurateGradientEvaluation := true }

/-- Hypothesized cancellation mechanism for the inaccurate sonar gradients. -/
structure P01SonarCancellationHypothesisReport where
  concernsInaccurateObjectiveGradientEvaluation : Bool
  mechanismPresentedAsPaperAuthorsHypothesis : Bool
  hypothesizedCauseIsRoundoffError : Bool
  roundoffErrorResultsFromCancellationOfObjectiveGradientTerms : Bool
  termsHaveApproximatelyEqualMagnitudes : Bool
  termsHaveOppositeSigns : Bool

def p01SonarCancellationHypothesisReport :
    P01SonarCancellationHypothesisReport :=
  { concernsInaccurateObjectiveGradientEvaluation := true
    mechanismPresentedAsPaperAuthorsHypothesis := true
    hypothesizedCauseIsRoundoffError := true
    roundoffErrorResultsFromCancellationOfObjectiveGradientTerms := true
    termsHaveApproximatelyEqualMagnitudes := true
    termsHaveOppositeSigns := true }

/-- Sign-separated accumulation protocol applied to each gradient component. -/
structure P01SonarSignSeparatedProtocolReport where
  concernsObjectiveGradientInCitedSum41 : Bool
  objectiveGradientIsSumOfMTerms : Bool
  appliedSeparatelyToEachObjectiveGradientComponent : Bool
  positiveAndNegativeTermsAccumulatedSeparately : Bool
  accumulatedSignBlocksAddedTogetherOnlyAfterAllMTermsProcessed : Bool

def p01SonarSignSeparatedProtocolReport :
    P01SonarSignSeparatedProtocolReport :=
  { concernsObjectiveGradientInCitedSum41 := true
    objectiveGradientIsSumOfMTerms := true
    appliedSeparatelyToEachObjectiveGradientComponent := true
    positiveAndNegativeTermsAccumulatedSeparately := true
    accumulatedSignBlocksAddedTogetherOnlyAfterAllMTermsProcessed := true }

/-- The intervention reported in the sonar application: for each gradient
component, positive and negative terms are accumulated separately and the two
subtotals are added only after all `M` terms have been processed. -/
inductive P01SonarGradientIntervention
  | separatePositiveAndNegativeTermsForEachComponentThenAddAfterAllMTerms

/-- The exact expression to which the reported intervention was applied. -/
inductive P01SonarGradientInterventionTarget
  | objectiveGradientSum41

/-- The two source-worded reports of what that intervention achieved. -/
inductive P01SonarReportedOutcome
  | eliminatedTheseOptimizerDifficulties
  | curedSomeInaccurateGradientProblemsInAnOptimizationMethod

/-- Reported outcome of the sign-separated sonar-gradient protocol, retaining
the initial elimination claim and the conclusion's weaker `some problems`
restatement as distinct outcomes. -/
structure P01SonarDifficultiesEliminatedReport where
  citedReferenceNumber : ℕ
  interventionTarget : P01SonarGradientInterventionTarget
  intervention : P01SonarGradientIntervention
  method : P01SummationMethod
  initialReport : P01SonarReportedOutcome
  conclusionReport : P01SonarReportedOutcome

def p01SonarDifficultiesEliminatedReport :
    P01SonarDifficultiesEliminatedReport :=
  { citedReferenceNumber := 24
    interventionTarget := .objectiveGradientSum41
    intervention :=
      .separatePositiveAndNegativeTermsForEachComponentThenAddAfterAllMTerms
    method := .plusMinus
    initialReport := .eliminatedTheseOptimizerDifficulties
    conclusionReport :=
      .curedSomeInaccurateGradientProblemsInAnOptimizationMethod }

/-- The paper separately assesses plus/minus summation as unattractive. -/
structure P01SonarPlusMinusAssessmentReport where
  concernsPlusMinusSummation : Bool
  contrastsWithReportedCureOfSomeInaccurateGradientProblems : Bool
  unattractivenessIsWhyReportedCureIsALittleSurprising : Bool
  paperFoundMethodUnattractive : Bool

def p01SonarPlusMinusAssessmentReport : P01SonarPlusMinusAssessmentReport :=
  { concernsPlusMinusSummation := true
    contrastsWithReportedCureOfSomeInaccurateGradientProblems := true
    unattractivenessIsWhyReportedCureIsALittleSurprising := true
    paperFoundMethodUnattractive := true }

/-- The reported sonar cure is described as surprising. -/
structure P01SonarSurpriseReport where
  concernsReportedCureByPlusMinusSummation : Bool
  reportedCureDescribedAsALittleSurprising : Bool

def p01SonarSurpriseReport : P01SonarSurpriseReport :=
  { concernsReportedCureByPlusMinusSummation := true
    reportedCureDescribedAsALittleSurprising := true }

/-- Apparent effect of an application feature on the method comparison. -/
structure P01SonarApplicationFeatureComparisonReport where
  featureBelongsToSonarApplication : Bool
  featureAppearsToFavorPlusMinusOverNaturalRecursiveSummation : Bool

def p01SonarApplicationFeatureComparisonReport :
    P01SonarApplicationFeatureComparisonReport :=
  { featureBelongsToSonarApplication := true
    featureAppearsToFavorPlusMinusOverNaturalRecursiveSummation := true }

/-- Separate epistemic status of the feature invoked in that comparison. -/
structure P01SonarApplicationFeatureNotApparentReport where
  concernsFeatureFavoringPlusMinusInSonarApplication : Bool
  citedReferenceNumber : ℕ
  featureIsApparentFromCitedSource : Bool

def p01SonarApplicationFeatureNotApparentReport :
    P01SonarApplicationFeatureNotApparentReport :=
  { concernsFeatureFavoringPlusMinusInSonarApplication := true
    citedReferenceNumber := 24
    featureIsApparentFromCitedSource := false }

/-- Search-direction symmetry loss observed in the quasi-Newton application. -/
structure P01DixonMillsSearchDirectionSymmetryLossReport where
  observationAttributedToReferenceSeven : Bool
  concernsExpectedSymmetryOfSearchDirection : Bool
  expectedSymmetryReportedLostInPractice : Bool

def p01DixonMillsSearchDirectionSymmetryLossReport :
    P01DixonMillsSearchDirectionSymmetryLossReport :=
  { observationAttributedToReferenceSeven := true
    concernsExpectedSymmetryOfSearchDirection := true
    expectedSymmetryReportedLostInPractice := true }

/-- The paired search-direction and Hessian-approximation symmetry loss. -/
structure P01DixonMillsHessianSymmetryLossReport where
  observationAttributedToReferenceSeven : Bool
  expectedSearchDirectionSymmetryReportedLostInPractice : Bool
  expectedHessianApproximationSymmetryReportedLostInPractice : Bool

def p01DixonMillsHessianSymmetryLossReport :
    P01DixonMillsHessianSymmetryLossReport :=
  { observationAttributedToReferenceSeven := true
    expectedSearchDirectionSymmetryReportedLostInPractice := true
    expectedHessianApproximationSymmetryReportedLostInPractice := true }

/-- The observed iteration impact of the symmetry loss. -/
structure P01DixonMillsIterationImpactReport where
  expectedSearchDirectionSymmetryLostInPractice : Bool
  expectedHessianApproximationSymmetryLostInPractice : Bool
  lossesCausedMoreIterationsForQuasiNewtonConvergence : Bool
  iterationCountExceededTheoreticalPrediction : Bool

def p01DixonMillsIterationImpactReport : P01DixonMillsIterationImpactReport :=
  { expectedSearchDirectionSymmetryLostInPractice := true
    expectedHessianApproximationSymmetryLostInPractice := true
    lossesCausedMoreIterationsForQuasiNewtonConvergence := true
    iterationCountExceededTheoreticalPrediction := true }

/-- Dixon and Mills's attribution of the symmetry loss. -/
structure P01DixonMillsRoundingAttributionReport where
  attributionMadeByDixonAndMills : Bool
  concernsLossOfExpectedSearchDirectionAndHessianApproximationSymmetries : Bool
  lossAttributedToRoundingErrors : Bool
  roundingErrorsAriseInEvaluationOfCertainInnerProducts : Bool

def p01DixonMillsRoundingAttributionReport :
    P01DixonMillsRoundingAttributionReport :=
  { attributionMadeByDixonAndMills := true
    concernsLossOfExpectedSearchDirectionAndHessianApproximationSymmetries := true
    lossAttributedToRoundingErrors := true
    roundingErrorsAriseInEvaluationOfCertainInnerProducts := true }

/-- Floating-point failure of identities such as the pair-swap symmetry
following the extended Rosenbrock formula (1.1). -/
structure P01DixonMillsFloatingPointIdentityFailureReport where
  causeIsRoundingErrorsInEvaluationOfCertainInnerProducts : Bool
  exampleIdentityIsQuotedRosenbrockPairSwapForNFour : Bool
  suchRoundingErrorsCanCauseTheIdentityToFailInFloatingPointArithmetic : Bool

def p01DixonMillsFloatingPointIdentityFailureReport :
    P01DixonMillsFloatingPointIdentityFailureReport :=
  { causeIsRoundingErrorsInEvaluationOfCertainInnerProducts := true
    exampleIdentityIsQuotedRosenbrockPairSwapForNFour := true
    suchRoundingErrorsCanCauseTheIdentityToFailInFloatingPointArithmetic := true }

/-- The reported restoration of the relevant symmetries. -/
structure P01DixonMillsSymmetryRestorationReport where
  procedureAttributedToDixonAndMills : Bool
  procedureCharacterizedAsSpecialSummationAlgorithm : Bool
  procedureUsedWhenEvaluatingInnerProducts : Bool
  procedureRestoredRelevantSymmetries : Bool

def p01DixonMillsSymmetryRestorationReport :
    P01DixonMillsSymmetryRestorationReport :=
  { procedureAttributedToDixonAndMills := true
    procedureCharacterizedAsSpecialSummationAlgorithm := true
    procedureUsedWhenEvaluatingInnerProducts := true
    procedureRestoredRelevantSymmetries := true }

/-- The reported reduction in iteration count. -/
structure P01DixonMillsIterationReductionReport where
  specialSummationProcedureUsedWhenEvaluatingInnerProducts : Bool
  specialSummationProcedureRestoredRelevantSymmetries : Bool
  restoredSymmetriesTherebyReducedIterationCount : Bool

def p01DixonMillsIterationReductionReport :
    P01DixonMillsIterationReductionReport :=
  { specialSummationProcedureUsedWhenEvaluatingInnerProducts := true
    specialSummationProcedureRestoredRelevantSymmetries := true
    restoredSymmetriesTherebyReducedIterationCount := true }

/-- One Dixon--Mills step: combine the largest nonnegative and most negative terms. -/
def P01DixonMillsStep
    (flAdd : ℝ → ℝ → ℝ) (xs ys : List ℝ) : Prop :=
  ∃ positive negative : ℝ, ∃ rest : List ℝ,
    xs.Perm (positive :: negative :: rest) ∧
    0 ≤ positive ∧ negative < 0 ∧
    (∀ z ∈ xs, 0 ≤ z → z ≤ positive) ∧
    (∀ z ∈ xs, z < 0 → negative ≤ z) ∧
    ys.Perm (flAdd positive negative :: rest) ∧
    (ys.Pairwise fun x y => x ≤ y)

/-- A Dixon--Mills residual at which no opposite-sign reduction remains. -/
def P01DixonMillsTerminal (xs : List ℝ) : Prop :=
  (∀ x ∈ xs, x < 0) ∨ (∀ x ∈ xs, 0 ≤ x)

/-- The source-specified initial sorting and division into ordered negative and
nonnegative lists.  Equal terms may occur in either order because the source
does not give a tie-breaking rule. -/
def P01DixonMillsPreparation
    (inputs negatives nonnegatives : List ℝ) : Prop :=
  (negatives ++ nonnegatives).Perm inputs ∧
  (∀ x ∈ negatives, x < 0) ∧ negatives.Pairwise (· ≤ ·) ∧
  (∀ x ∈ nonnegatives, 0 ≤ x) ∧ nonnegatives.Pairwise (· ≤ ·)

/-- Zero or more source-specified opposite-sign combinations with ordered
reinsertion after each combination. -/
def P01DixonMillsRepeatedReduction
    (flAdd : ℝ → ℝ → ℝ) (start residual : List ℝ) : Prop :=
  Relation.ReflTransGen (P01DixonMillsStep flAdd) start residual

/-- A terminal evaluation that preserves the maintained list order.  All
binary associations are admitted because the source excerpt does not choose
one after the opposite-sign phase ends. -/
inductive P01OrderPreservingEvaluation
    (flAdd : ℝ → ℝ → ℝ) : List ℝ → ℝ → Prop
  | empty : P01OrderPreservingEvaluation flAdd [] 0
  | singleton (x : ℝ) : P01OrderPreservingEvaluation flAdd [x] x
  | append (left right : List ℝ) (leftResult rightResult : ℝ)
      (hleft : left ≠ []) (hright : right ≠ [])
      (evalLeft : P01OrderPreservingEvaluation flAdd left leftResult)
      (evalRight : P01OrderPreservingEvaluation flAdd right rightResult) :
      P01OrderPreservingEvaluation flAdd (left ++ right)
        (flAdd leftResult rightResult)

/-- The Dixon--Mills evaluation relation: perform exactly the stated ordered
opposite-sign reductions, then finish without changing the remaining order.
The terminal association remains deliberately unspecified, as in the source. -/
def P01DixonMillsReduction
    (fp : P01StandardAddModel) (inputs : List ℝ) (result : ℝ) : Prop :=
  ∃ negatives nonnegatives residual : List ℝ,
    P01DixonMillsPreparation inputs negatives nonnegatives ∧
    P01DixonMillsRepeatedReduction
      fp.fl_add (negatives ++ nonnegatives) residual ∧
    P01DixonMillsTerminal residual ∧
    P01OrderPreservingEvaluation fp.fl_add residual result

/-- The source-specified sorting and sign-list preparation in the Dixon--Mills procedure. -/
def p01DixonMillsTieBreakingSpecificationReport
    (inputs negatives nonnegatives : List ℝ) : Prop :=
  P01DixonMillsPreparation inputs negatives nonnegatives

/-- The source-specified repeated combination and ordered reinsertion step. -/
def p01DixonMillsTerminalReductionSpecificationReport
    (flAdd : ℝ → ℝ → ℝ) (inputs negatives nonnegatives residual : List ℝ) : Prop :=
  P01DixonMillsPreparation inputs negatives nonnegatives ∧
  P01DixonMillsRepeatedReduction
    flAdd (negatives ++ nonnegatives) residual

/-- Pairwise summation is attractive in parallel settings because every stage is parallelizable. -/
structure P01PairwiseParallelStageReport where
  concernsPairwiseSummationStages : Bool
  pairwiseSummationReportedAttractiveInParallelSettings : Bool
  attractivenessReasonIsEveryStageParallelizable : Bool
  everyStageReportedParallelizable : Bool

def p01PairwiseParallelStageReport : P01PairwiseParallelStageReport :=
  { concernsPairwiseSummationStages := true
    pairwiseSummationReportedAttractiveInParallelSettings := true
    attractivenessReasonIsEveryStageParallelizable := true
    everyStageReportedParallelizable := true }

/-- Caprani serial implementation and its storage behavior. -/
structure P01PairwiseSerialImplementationReport where
  coherentSerialImplementationReportedToExist : Bool
  implementationOverwritesInputs : Bool
  temporaryStorageForLength : ℕ → ℕ
  storageReportedAsCeilingLogTwoOfLength : Bool

def p01PairwiseSerialImplementationReport :
    P01PairwiseSerialImplementationReport :=
  { coherentSerialImplementationReportedToExist := true
    implementationOverwritesInputs := false
    temporaryStorageForLength := p01CeilLog2
    storageReportedAsCeilingLogTwoOfLength := true }

/-- The no-guard model (5.1), including both printed addition and subtraction signs. -/
structure P01NoGuardAddSubModel where
  u : ℝ
  u_pos : 0 < u
  flAdd : ℝ → ℝ → ℝ
  flSub : ℝ → ℝ → ℝ
  add_model : ∀ x y, ∃ α β : ℝ,
    |α| ≤ u ∧ |β| ≤ u ∧ flAdd x y = x * (1 + α) + y * (1 + β)
  sub_model : ∀ x y, ∃ α β : ℝ,
    |α| ≤ u ∧ |β| ≤ u ∧ flSub x y = x * (1 + α) - y * (1 + β)

/-- Malcolm [28] is reported to establish order-u relative error by a
detailed error analysis of his accumulator method. -/
structure P01MalcolmOrderUAccuracyReport where
  concernsMalcolmAccumulatorMethod : Bool
  detailedErrorAnalysisAttributedToMalcolm : Bool
  citationReference : ℕ
  analysisShowsMethodAchievesRelativeErrorOrderU : Bool

def p01MalcolmOrderUAccuracyReport : P01MalcolmOrderUAccuracyReport :=
  { concernsMalcolmAccumulatorMethod := true
    detailedErrorAnalysisAttributedToMalcolm := true
    citationReference := 28
    analysisShowsMethodAchievesRelativeErrorOrderU := true }

/-- The source explicitly calls strong machine dependence a drawback. -/
structure P01MalcolmMachineDependenceReport where
  concernsMalcolmAccumulatorMethod : Bool
  stronglyMachineDependent : Bool
  strongMachineDependenceReportedAsDrawback : Bool

def p01MalcolmMachineDependenceReport : P01MalcolmMachineDependenceReport :=
  { concernsMalcolmAccumulatorMethod := true
    stronglyMachineDependent := true
    strongMachineDependenceReportedAsDrawback := true }

/-- Characterization of Malcolm's actual final-step accumulator reduction. -/
structure P01MalcolmFinalOrderCharacterizationReport where
  malcolmAlgorithmFinalStepRecursivelySumsAccumulatorsInDecreasingAbsoluteMagnitude : Bool
  featureCharacterizedAsInterestingAndCrucial : Bool

def p01MalcolmFinalOrderCharacterizationReport :
    P01MalcolmFinalOrderCharacterizationReport :=
  { malcolmAlgorithmFinalStepRecursivelySumsAccumulatorsInDecreasingAbsoluteMagnitude := true
    featureCharacterizedAsInterestingAndCrucial := true }

/-- Effect of the decreasing-magnitude final-level order on significant-digit loss. -/
structure P01MalcolmFinalOrderDigitLossReport where
  concernsRecursiveFinalLevelSummationInDecreasingAbsoluteMagnitude : Bool
  orderingReportedToPrecludeSevereSignificantDigitLoss : Bool

def p01MalcolmFinalOrderDigitLossReport :
    P01MalcolmFinalOrderDigitLossReport :=
  { concernsRecursiveFinalLevelSummationInDecreasingAbsoluteMagnitude := true
    orderingReportedToPrecludeSevereSignificantDigitLoss := true }

/-- Separate small-relative-error guarantee attributed to the same final-level order. -/
structure P01MalcolmFinalOrderSmallErrorReport where
  concernsRecursiveFinalLevelSummationInDecreasingAbsoluteMagnitude : Bool
  orderingReportedToGuaranteeSmallRelativeError : Bool

def p01MalcolmFinalOrderSmallErrorReport :
    P01MalcolmFinalOrderSmallErrorReport :=
  { concernsRecursiveFinalLevelSummationInDecreasingAbsoluteMagnitude := true
    orderingReportedToGuaranteeSmallRelativeError := true }

/-- Average-running-time lower order used in Kahan's distillation report. -/
def P01AverageRuntimeAtLeastNLogN (runtime : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, ∀ n, n0 ≤ n →
    c * (n : ℝ) * Nat.log 2 n ≤ runtime n

/-- Attributed and explicitly tentative report about the plural class of
distillation algorithms. -/
structure P01DistillationRuntimeConjectureReport where
  concernsDistillationAlgorithms : Bool
  appliesToEachAlgorithmInThatClass : Bool
  averageRuntimeLowerOrder : (ℕ → ℝ) → Prop
  averageRuntimeLowerOrder_eq :
    averageRuntimeLowerOrder = P01AverageRuntimeAtLeastNLogN
  claimAttributedToKahan : Bool
  citationReference : ℕ
  sourceUsesTentativeAppearLanguage : Bool

def P01DistillationRuntimeConjecture :
    P01DistillationRuntimeConjectureReport :=
  { concernsDistillationAlgorithms := true
    appliesToEachAlgorithmInThatClass := true
    averageRuntimeLowerOrder := P01AverageRuntimeAtLeastNLogN
    averageRuntimeLowerOrder_eq := rfl
    claimAttributedToKahan := true
    citationReference := 19
    sourceUsesTentativeAppearLanguage := true }

/-- Table 6.1 input, cancellation-ratio functional `|sum xᵢ| / sum |xᵢ|`, and reported value `3.48e-6`. -/
noncomputable def p01Table61CancellationRatio :
    (Fin 64 → ℝ) × ((Fin 64 → ℝ) → ℝ) × ℚ :=
  (p01Table61Input,
    fun x => |p01ExactSum 64 x| / p01AbsoluteSum 64 x,
    348 / 100000000)

/-- The two cancellation ratios reported for the normal data in Table 6.2. -/
structure P01Table62CancellationRatioReport where
  setup : P01Table62SetupReport
  ratioIsAbsoluteExactSumOverAbsoluteInputSum : Bool
  normal2048 : ℚ
  normal4096 : ℚ

def p01Table62CancellationRatios : P01Table62CancellationRatioReport :=
  { setup := p01Table62SetupReport
    ratioIsAbsoluteExactSumOverAbsoluteInputSum := true
    normal2048 := 808 / 100000
    normal4096 := 348 / 100000 }

/-- The approximately reported normwise condition number of the triangular
matrix. -/
structure P01ForwardNormwiseConditionReport where
  concernsTestedTriangularMatrix : Bool
  usesMatrixAndVectorInfinityNorms : Bool
  reportedValue : ℚ
  reportedApproximately : Bool
  approximationToleranceSpecified : Bool

def p01ForwardNormwiseConditionReport : P01ForwardNormwiseConditionReport :=
  { concernsTestedTriangularMatrix := true
    usesMatrixAndVectorInfinityNorms := true
    reportedValue := 30000000
    reportedApproximately := true
    approximationToleranceSpecified := false }

/-- The approximately reported componentwise condition numbers for the two
specified right-hand sides. -/
structure P01ForwardComponentwiseConditionReport where
  concernsTestedTriangularMatrix : Bool
  systems : List P01ForwardSystem
  valuesAreForComponentwiseTriangularCondition : Bool
  firstSystemReportedValue : ℚ
  secondSystemReportedValue : ℚ
  valuesReportedApproximately : Bool
  approximationToleranceSpecified : Bool

def p01ForwardComponentwiseConditionReport :
    P01ForwardComponentwiseConditionReport :=
  { concernsTestedTriangularMatrix := true
    systems := [.first, .second]
    valuesAreForComponentwiseTriangularCondition := true
    firstSystemReportedValue := 700000
    secondSystemReportedValue := 700000
    valuesReportedApproximately := true
    approximationToleranceSpecified := false }

/-- The empirical statement that each tested method could be driven to no correct digits. -/
structure P01MDSAllMethodsFailureReport where
  dimension : ℕ
  precedingTwoExamplesReportedTypical : Bool
  usesMDSMaximizer : Bool
  dataReportedStraightforwardToFind : Bool
  noCorrectSignificantFiguresFoundFor : P01SummationMethod → Bool

def p01MDSReportedTotalFailure : P01MDSAllMethodsFailureReport :=
  { dimension := 3
    precedingTwoExamplesReportedTypical := true
    usesMDSMaximizer := true
    dataReportedStraightforwardToFind := true
    noCorrectSignificantFiguresFoundFor := fun _ => true }

/-- The second MDS vector's reported objective after increasing/decreasing reordering. -/
structure P01MDSReorderingObjectiveReport where
  sourceReport : P01MDSReport
  sourceVectorIsSecondLocatedMDSVector : Bool
  firstOrdering : P01SummationMethod
  increasingObjective : ℚ
  secondOrdering : P01SummationMethod
  decreasingObjective : ℚ

def p01MDSSecondReorderingObjectives : P01MDSReorderingObjectiveReport :=
  { sourceReport := p01MDSCompensatedReport
    sourceVectorIsSecondLocatedMDSVector := true
    firstOrdering := .increasing
    increasingObjective := 1
    secondOrdering := .decreasing
    decreasingObjective := 0 }

/-- The abstract's negative uniform-accuracy-superiority claim. -/
structure P01UniformAccuracySuperiorityReport where
  comparisonScopeIsSummationMethodsConsideredInPaper : Bool
  comparisonMethodSetEnumeratedAtClaim : Bool
  anyMethodUniformlyMoreAccurateThanOthers : Bool

def p01UniformAccuracySuperiorityReport : P01UniformAccuracySuperiorityReport :=
  { comparisonScopeIsSummationMethodsConsideredInPaper := true
    comparisonMethodSetEnumeratedAtClaim := false
    anyMethodUniformlyMoreAccurateThanOthers := false }

/-- The conclusion's separate observation about data-dependent variability. -/
structure P01AccuracyVariabilityWithinBoundsReport where
  methods : List P01SummationMethod
  errorsCanVaryGreatlyWithDataWithinBoundsForEachMethod : Bool

def p01AccuracyVariabilityWithinBoundsReport :
    P01AccuracyVariabilityWithinBoundsReport :=
  { methods :=
      [.original, .increasing, .decreasing, .psum, .pairwise, .insertion, .plusMinus,
        .compensated]
    errorsCanVaryGreatlyWithDataWithinBoundsForEachMethod := true }

/-- The linear worst-case growth assigned to methods other than pairwise and
compensated summation. -/
structure P01NonPairwiseNoncompensatedWorstCaseGrowthReport where
  methods : List P01SummationMethod
  worstCaseErrorProportionalToNForEachMethod : Bool

def p01NonPairwiseNoncompensatedWorstCaseGrowthReport :
    P01NonPairwiseNoncompensatedWorstCaseGrowthReport :=
  { methods := [.original, .increasing, .decreasing, .psum, .insertion, .plusMinus]
    worstCaseErrorProportionalToNForEachMethod := true }

/-- The logarithmic worst-case leading coefficient assigned to pairwise
summation. -/
structure P01PairwiseWorstCaseGrowthReport where
  appliesToPairwiseSummation : Bool
  worstCaseLeadingCoefficientLogarithmic : Bool
  reportedLeadingCoefficient : ℕ → ℕ

def p01PairwiseWorstCaseGrowthReport : P01PairwiseWorstCaseGrowthReport :=
  { appliesToPairwiseSummation := true
    worstCaseLeadingCoefficientLogarithmic := true
    reportedLeadingCoefficient := p01CeilLog2 }

/-- The order-one worst-case leading coefficient assigned to compensated
summation. -/
structure P01CompensatedWorstCaseGrowthReport where
  appliesToCompensatedSummation : Bool
  worstCaseLeadingCoefficientOrderOne : Bool

def p01CompensatedWorstCaseGrowthReport : P01CompensatedWorstCaseGrowthReport :=
  { appliesToCompensatedSummation := true
    worstCaseLeadingCoefficientOrderOne := true }

/-- Shared applicability scope for the very-large-n recommendations. -/
structure P01VeryLargeNScopeReport where
  appliesWhenNIsVeryLarge : Bool

def p01VeryLargeNScopeReport : P01VeryLargeNScopeReport :=
  { appliesWhenNIsVeryLarge := true }

/-- Pairwise recommendation in the very-large-n regime. -/
structure P01VeryLargeNPairwiseAttractivenessReport where
  scope : P01VeryLargeNScopeReport
  pairwiseSummationReportedAttractive : Bool

def p01VeryLargeNPairwiseAttractivenessReport :
    P01VeryLargeNPairwiseAttractivenessReport :=
  { scope := p01VeryLargeNScopeReport
    pairwiseSummationReportedAttractive := true }

/-- Compensated recommendation in the same very-large-n regime. -/
structure P01VeryLargeNCompensatedAttractivenessReport where
  scope : P01VeryLargeNScopeReport
  compensatedSummationReportedAttractive : Bool

def p01VeryLargeNCompensatedAttractivenessReport :
    P01VeryLargeNCompensatedAttractivenessReport :=
  { scope := p01VeryLargeNScopeReport
    compensatedSummationReportedAttractive := true }

/-- The conclusion's all-method bound for one-signed inputs. -/
structure P01OneSignedAllMethodsBoundReport where
  appliesToOneSignedInputs : Bool
  methods : List P01SummationMethod
  relativeErrorReportedAtMostNUnitRoundoffsForEachMethod : Bool

def p01OneSignedAllMethodsBoundReport : P01OneSignedAllMethodsBoundReport :=
  { appliesToOneSignedInputs := true
    methods :=
      [.original, .increasing, .decreasing, .psum, .pairwise, .insertion, .plusMinus,
        .compensated]
    relativeErrorReportedAtMostNUnitRoundoffsForEachMethod := true }

/-- The conclusion's ordering recommendation for one-signed recursive data. -/
structure P01OneSignedOrderingRecommendationReport where
  appliesToOneSignedRecursiveSummation : Bool
  increasingPreferredToDecreasing : Bool

def p01OneSignedOrderingRecommendationReport :
    P01OneSignedOrderingRecommendationReport :=
  { appliesToOneSignedRecursiveSummation := true
    increasingPreferredToDecreasing := true }

/-- The conclusion's insertion claim broadens the earlier positive-input
assertion to all one-signed data and explicitly excludes compensated summation. -/
structure P01OneSignedInsertionOptimalityConclusionReport where
  appliesToInputsWhoseEntriesAllHaveTheSameSign : Bool
  comparedMethods : List P01SummationMethod
  insertionClaimedSmallestEquation34BoundAmongComparedMethods : Bool

def p01OneSignedInsertionOptimalityConclusionReport :
    P01OneSignedInsertionOptimalityConclusionReport :=
  { appliesToInputsWhoseEntriesAllHaveTheSameSign := true
    comparedMethods :=
      [.original, .increasing, .decreasing, .psum, .pairwise, .insertion, .plusMinus]
    insertionClaimedSmallestEquation34BoundAmongComparedMethods := true }

/-- The pre-section-3 likelihood claim for decreasing order under heavy
cancellation. -/
structure P01DecreasingHeavyCancellationLikelihoodReport where
  scope : P01HeavyCancellationScopeReport
  comparedAgainstIncreasingAndPsumOrderings : Bool
  decreasingOrderLikelyMoreAccurate : Bool

noncomputable def p01DecreasingHeavyCancellationLikelihoodReport :
    P01DecreasingHeavyCancellationLikelihoodReport :=
  { scope := p01HeavyCancellationScopeReport
    comparedAgainstIncreasingAndPsumOrderings := true
    decreasingOrderLikelyMoreAccurate := true }

/-- The expected relative ranking of plus/minus summation under heavy
cancellation. -/
structure P01PlusMinusHeavyCancellationExpectationReport where
  scope : P01HeavyCancellationScopeReport
  noAdvantagesAssessment : P01PlusMinusNoAdvantagesAssessmentReport
  comparisonClassIsOtherMethodsConsideredHere : Bool
  plusMinusExpectedLeastAccurateUnderHeavyCancellation : Bool

noncomputable def p01PlusMinusHeavyCancellationExpectationReport :
    P01PlusMinusHeavyCancellationExpectationReport :=
  { scope := p01HeavyCancellationScopeReport
    noAdvantagesAssessment := p01PlusMinusNoAdvantagesAssessmentReport
    comparisonClassIsOtherMethodsConsideredHere := true
    plusMinusExpectedLeastAccurateUnderHeavyCancellation := true }

/-- Qualitative attraction of decreasing recursive order under heavy cancellation. -/
structure P01DecreasingHeavyCancellationAttractivenessReport where
  scope : P01HeavyCancellationScopeReport
  concernsRecursiveSummationInDecreasingMagnitudeOrder : Bool
  decreasingOrderReportedAttractive : Bool

noncomputable def p01DecreasingHeavyCancellationAttractivenessReport :
    P01DecreasingHeavyCancellationAttractivenessReport :=
  { scope := p01HeavyCancellationScopeReport
    concernsRecursiveSummationInDecreasingMagnitudeOrder := true
    decreasingOrderReportedAttractive := true }

/-- Separate absence of a best-accuracy guarantee under heavy cancellation. -/
structure P01DecreasingHeavyCancellationNoBestGuaranteeReport where
  scope : P01HeavyCancellationScopeReport
  concernsRecursiveSummationInDecreasingMagnitudeOrder : Bool
  guaranteedToAchieveBestAccuracy : Bool

noncomputable def p01DecreasingHeavyCancellationNoBestGuaranteeReport :
    P01DecreasingHeavyCancellationNoBestGuaranteeReport :=
  { scope := p01HeavyCancellationScopeReport
    concernsRecursiveSummationInDecreasingMagnitudeOrder := true
    guaranteedToAchieveBestAccuracy := false }

/-- The methods explicitly reported to require only linear operation count. -/
structure P01LinearOperationCostReport where
  appliesToGeneralInputData : Bool
  naturalRecursiveLinearOperations : Bool
  pairwiseLinearOperations : Bool
  compensatedLinearOperations : Bool

def p01LinearOperationCostReport : P01LinearOperationCostReport :=
  { appliesToGeneralInputData := true
    naturalRecursiveLinearOperations := true
    pairwiseLinearOperations := true
    compensatedLinearOperations := true }

/-- The search-or-sort overhead assigned to the other considered orderings. -/
structure P01OrderingOverheadReport where
  methodsRequiringSearchingOrSorting : List P01SummationMethod
  methodsReportedMoreExpensiveBecauseTheyRequireSearchingOrSorting : Bool

def p01OrderingOverheadReport : P01OrderingOverheadReport :=
  { methodsRequiringSearchingOrSorting :=
      [.increasing, .decreasing, .psum, .insertion, .plusMinus]
    methodsReportedMoreExpensiveBecauseTheyRequireSearchingOrSorting := true }

/-- The source's sequential-data obstruction to reordering an entire input. -/
structure P01SequentialGenerationConstraintReport where
  applicationIsNumericalSolutionOfOrdinaryDifferentialEquations : Bool
  inputsAreGeneratedSequentially : Bool
  termMayDependOnSumOfAllEarlierTerms : Bool
  generationCanPrecludeSearchingOrSorting : Bool

def p01SequentialGenerationConstraintReport :
    P01SequentialGenerationConstraintReport :=
  { applicationIsNumericalSolutionOfOrdinaryDifferentialEquations := true
    inputsAreGeneratedSequentially := true
    termMayDependOnSumOfAllEarlierTerms := true
    generationCanPrecludeSearchingOrSorting := true }

/-- Shared feasibility and comparator scope for the higher-precision guidance. -/
structure P01HigherPrecisionRecursiveComparisonScope where
  higherPrecisionRecursiveSummationIsFeasible : Bool
  comparatorIsAnAlternativeMethodInWorkingPrecision : Bool

def p01HigherPrecisionRecursiveComparisonScope :
    P01HigherPrecisionRecursiveComparisonScope :=
  { higherPrecisionRecursiveSummationIsFeasible := true
    comparatorIsAnAlternativeMethodInWorkingPrecision := true }

/-- Qualified cost comparison for feasible higher-precision recursion. -/
structure P01HigherPrecisionRecursiveCostReport where
  scope : P01HigherPrecisionRecursiveComparisonScope
  mayBeLessExpensive : Bool

def p01HigherPrecisionRecursiveCostReport :
    P01HigherPrecisionRecursiveCostReport :=
  { scope := p01HigherPrecisionRecursiveComparisonScope
    mayBeLessExpensive := true }

/-- Separate qualified accuracy comparison over the same explicit scope. -/
structure P01HigherPrecisionRecursiveAccuracyReport where
  scope : P01HigherPrecisionRecursiveComparisonScope
  mayBeMoreAccurate : Bool

def p01HigherPrecisionRecursiveAccuracyReport :
    P01HigherPrecisionRecursiveAccuracyReport :=
  { scope := p01HigherPrecisionRecursiveComparisonScope
    mayBeMoreAccurate := true }

/-- The two nonempty, increasing-magnitude sign blocks that are the complete
hypothesis of the equation-(3.8) plus/minus estimate. -/
structure P01Equation38OrderedSignBlocks
    (p q : ℕ) (negative : Fin p → ℝ) (nonnegative : Fin q → ℝ) where
  negativeBlockNonempty : 0 < p
  nonnegativeBlockNonempty : 0 < q
  negativeEntriesStrictlyNegative : ∀ i, negative i < 0
  nonnegativeEntriesNonnegative : ∀ i, 0 ≤ nonnegative i
  negativeBlockIncreasingMagnitude : P01MagnitudeNondecreasing negative
  nonnegativeBlockIncreasingMagnitude : P01MagnitudeNondecreasing nonnegative

/-- Kahan's printed two-output correction construction before (3.9), stated
for an arbitrary floating-point rounding operation and restricted exactly to
floating inputs satisfying the displayed magnitude premise. -/
noncomputable def p01FastTwoSumConstruction
    (fl : ℝ → ℝ) (isFloat : ℝ → Prop) (a b : ℝ)
    (_ha : isFloat a) (_hb : isFloat b) (_hmag : |b| ≤ |a|) : ℝ × ℝ :=
  let sumHat := fl (a + b)
  let correctionHat := -(fl (fl (sumHat - a) - b))
  (sumHat, correctionHat)

/-- The conclusion's separate, unqualified negative accuracy-superiority claim. -/
structure P01ConclusionAccuracySuperiorityReport where
  comparisonScopeIsSummationMethodsConsideredInPaper : Bool
  comparisonMethodSetEnumeratedAtClaim : Bool
  anyConsideredMethodRegardedAsSuperiorToRestInAccuracy : Bool

def p01ConclusionAccuracySuperiorityReport :
    P01ConclusionAccuracySuperiorityReport :=
  { comparisonScopeIsSummationMethodsConsideredInPaper := true
    comparisonMethodSetEnumeratedAtClaim := false
    anyConsideredMethodRegardedAsSuperiorToRestInAccuracy := false }

end HighamBench
