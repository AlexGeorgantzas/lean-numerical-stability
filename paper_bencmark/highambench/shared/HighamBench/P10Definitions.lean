import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped BigOperators Matrix.Norms.Frobenius

namespace HighamBench

/-- A square real matrix in the native finite `Matrix` representation. -/
abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite square matrix multiplication. -/
noncomputable def p10MatMul (n : ℕ) (A B : P10Matrix n) : P10Matrix n :=
  A * B

/-- The Frobenius norm, written explicitly to keep the public statement lightweight. -/
noncomputable def p10FrobNorm {n : ℕ} (A : P10Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- An otherwise unspecified matrix norm with the consistency properties used
in the paper's normwise product analysis. -/
structure P10ConsistentMatrixNorm (n : ℕ) where
  value : P10Matrix n → ℝ
  value_nonneg : ∀ A, 0 ≤ value A
  value_eq_zero_iff : ∀ A, value A = 0 ↔ A = 0
  value_smul : ∀ (c : ℝ) A, value (c • A) = |c| * value A
  value_add_le : ∀ A B, value (A + B) ≤ value A + value B
  value_matMul_le : ∀ A B,
    value (p10MatMul n A B) ≤ value A * value B

/-- One stable matrix-product computation with inherited operand errors.  The
cross term and the local higher-order remainder are retained in the execution
model but excluded from its first-order error. -/
structure P10FirstOrderProductRun (n : ℕ) where
  dimension_pos : 0 < n
  matrixNorm : P10ConsistentMatrixNorm n
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mu : ℕ → ℝ
  mu_nonneg : ∀ k, 0 ≤ mu k
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ k,
    mu k ≤ muGrowthConstant * (k : ℝ) ^ muDegree
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10Matrix n
  rightPerturbation : P10Matrix n
  computedProduct : P10Matrix n
  localFirstOrderError : P10Matrix n
  higherOrderRemainder : P10Matrix n
  leftInheritedError : ℝ
  rightInheritedError : ℝ
  leftInheritedError_nonneg : 0 ≤ leftInheritedError
  rightInheritedError_nonneg : 0 ≤ rightInheritedError
  higherOrderCoeff : ℝ
  higherOrderCoeff_nonneg : 0 ≤ higherOrderCoeff
  computed_product :
    computedProduct =
      p10MatMul n
          (exactLeft + leftPerturbation)
          (exactRight + rightPerturbation) +
        localFirstOrderError + higherOrderRemainder
  local_error_bound :
    matrixNorm.value localFirstOrderError ≤
      mu n * epsilon * matrixNorm.value exactLeft * matrixNorm.value exactRight
  left_inherited_error_bound :
    matrixNorm.value leftPerturbation ≤ leftInheritedError
  right_inherited_error_bound :
    matrixNorm.value rightPerturbation ≤ rightInheritedError
  higher_order_bound :
    matrixNorm.value higherOrderRemainder ≤ higherOrderCoeff * epsilon ^ 2

/-- The realized product error with the inherited cross term and the local
higher-order remainder removed, exactly as required by first-order analysis. -/
noncomputable def p10FirstOrderProductError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  run.computedProduct - p10MatMul n run.exactLeft run.exactRight -
      p10MatMul n run.leftPerturbation run.rightPerturbation -
    run.higherOrderRemainder

/-- The three first-order contributions printed in equation (8). -/
noncomputable def p10FirstOrderProductErrorBudget {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
      run.matrixNorm.value run.exactRight +
    (run.matrixNorm.value run.exactLeft * run.rightInheritedError +
      run.leftInheritedError * run.matrixNorm.value run.exactRight)

/-- The inherited-right error matrix produced to first order by multiplying
the right operand perturbation on the left by the exact left operand. -/
noncomputable def p10InheritedRightError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.exactLeft run.rightPerturbation

/-- Equation (8)'s local stable-multiplication contribution. -/
noncomputable def p10LocalProductErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.mu n * run.epsilon * run.matrixNorm.value run.exactLeft *
    run.matrixNorm.value run.exactRight

/-- Equation (8)'s inherited-right contribution `||A||*err(B,n)`. -/
noncomputable def p10InheritedRightErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.matrixNorm.value run.exactLeft * run.rightInheritedError

/-- Equation (8)'s inherited-left contribution `err(A,n)*||B||`. -/
noncomputable def p10InheritedLeftErrorContribution {n : ℕ}
    (run : P10FirstOrderProductRun n) : ℝ :=
  run.leftInheritedError * run.matrixNorm.value run.exactRight

/-- The selected inherited-right term, including both its propagated matrix
bound and its exact additive position in equation (8)'s first-order budget. -/
def P10InheritedRightEquation8Term {n : ℕ}
    (run : P10FirstOrderProductRun n) : Prop :=
  run.matrixNorm.value (p10InheritedRightError run) ≤
      p10InheritedRightErrorContribution run ∧
    p10FirstOrderProductErrorBudget run =
      p10LocalProductErrorContribution run +
        (p10InheritedRightErrorContribution run +
          p10InheritedLeftErrorContribution run)

/-- The one-level amplification factor in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterGrowth {n : ℕ}
    (A B : P10Matrix n) (sep : ℝ) : ℝ :=
  4 + 2 * (p10FrobNorm A + p10FrobNorm B) / sep

/-- The one-level forcing term in the Sylvester recurrence on printed page 86. -/
noncomputable def p10SylvesterForcing {n : ℕ}
    (A B C R : P10Matrix n) (sep epsilon mu : ℝ) : ℝ :=
  epsilon / sep *
    (3 * p10FrobNorm C +
      2 * mu * (p10FrobNorm A + p10FrobNorm B) * p10FrobNorm R)

/-! ## Recursive Sylvester solver model -/

/-- Recursive index set for a matrix of dimension exactly `2^depth`. -/
def P10DyadicIndex : ℕ → Type
  | 0 => Fin 1
  | depth + 1 => P10DyadicIndex depth ⊕ P10DyadicIndex depth

noncomputable instance p10DyadicIndexFintype (depth : ℕ) :
    Fintype (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : Fintype (P10DyadicIndex depth) := ih
      infer_instance

noncomputable instance p10DyadicIndexDecidableEq (depth : ℕ) :
    DecidableEq (P10DyadicIndex depth) := by
  induction depth with
  | zero =>
      simp only [P10DyadicIndex]
      infer_instance
  | succ depth ih =>
      simp only [P10DyadicIndex]
      letI : DecidableEq (P10DyadicIndex depth) := ih
      infer_instance

/-- A square real matrix of power-of-two dimension. -/
abbrev P10DyadicMatrix (depth : ℕ) :=
  Matrix (P10DyadicIndex depth) (P10DyadicIndex depth) ℝ

/-- The Frobenius norm used in the paper's definition of `sep(A,B)`. -/
noncomputable def p10DyadicFrobNorm {depth : ℕ}
    (A : P10DyadicMatrix depth) : ℝ :=
  letI : NormedRing (P10DyadicMatrix depth) :=
    Matrix.frobeniusNormedRing
  ‖A‖

noncomputable def p10DyadicBlock11 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₁ A

noncomputable def p10DyadicBlock12 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₁₂ A

noncomputable def p10DyadicBlock21 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₁ A

noncomputable def p10DyadicBlock22 {depth : ℕ}
    (A : P10DyadicMatrix (depth + 1)) : P10DyadicMatrix depth :=
  Matrix.toBlocks₂₂ A

/-- The Sylvester operator `X ↦ A*X-X*B`. -/
noncomputable def p10SylvesterAction {depth : ℕ}
    (A B X : P10DyadicMatrix depth) : P10DyadicMatrix depth :=
  A * X - X * B

/-- Certificate for the Frobenius variational definition of `sep(A,B)`. -/
structure P10SylvesterSeparation {depth : ℕ}
    (A B : P10DyadicMatrix depth) where
  value : ℝ
  value_pos : 0 < value
  lower_bound : ∀ X,
    value * p10DyadicFrobNorm X ≤
      p10DyadicFrobNorm (p10SylvesterAction A B X)
  attained : ∃ X,
    p10DyadicFrobNorm X = 1 ∧
      p10DyadicFrobNorm (p10SylvesterAction A B X) = value

/-- One exact Sylvester problem and its first-order computed SylR result.
Real-valued states model the standard finite regime: exceptional values and
the higher-order terms suppressed by the paper are outside this certificate. -/
structure P10SylRProblem (depth : ℕ) where
  A : P10DyadicMatrix depth
  B : P10DyadicMatrix depth
  C : P10DyadicMatrix depth
  exactSolution : P10DyadicMatrix depth
  computedSolution : P10DyadicMatrix depth
  exact_equation :
    p10SylvesterAction A B exactSolution = -C
  separation : P10SylvesterSeparation A B

/-- Absolute Frobenius forward error in the paper's first-order model. -/
noncomputable def p10SylRForwardError {depth : ℕ}
    (problem : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm (problem.computedSolution - problem.exactSolution)

noncomputable def p10SylRExactRhs11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock11 parent.C +
    p10DyadicBlock12 parent.A * p10DyadicBlock21 parent.exactSolution

noncomputable def p10SylRExactRhs22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock22 parent.C -
    p10DyadicBlock21 parent.exactSolution * p10DyadicBlock12 parent.B

noncomputable def p10SylRExactRhs12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1)) : P10DyadicMatrix depth :=
  p10DyadicBlock12 parent.C -
      p10DyadicBlock11 parent.exactSolution * p10DyadicBlock12 parent.B +
    p10DyadicBlock12 parent.A * p10DyadicBlock22 parent.exactSolution

/-- Total error in a computed child block, measured against the corresponding
block of the exact parent solution.  This includes rounded-RHS error. -/
noncomputable def p10SylRBlockError21 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock21 parent.exactSolution)

noncomputable def p10SylRBlockError11 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock11 parent.exactSolution)

noncomputable def p10SylRBlockError22 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock22 parent.exactSolution)

noncomputable def p10SylRBlockError12 {depth : ℕ}
    (parent : P10SylRProblem (depth + 1))
    (child : P10SylRProblem depth) : ℝ :=
  p10DyadicFrobNorm
    (child.computedSolution - p10DyadicBlock12 parent.exactSolution)

/-- One non-base SylR node and the four page-86 first-order block estimates.
The fields expose the solve order `R21`, `R11`, `R22`, `R12`, exact right-hand
sides (15)--(18), product model (8), and separation inequality (19). -/
structure P10SylRLevelCertificate {depth : ℕ}
    (epsilon muHalf smallerError globalANorm globalBNorm globalCNorm
      globalRNorm globalSep : ℝ)
    (parent : P10SylRProblem (depth + 1))
    (child21 child11 child22 child12 : P10SylRProblem depth) where
  parent_A21_zero : p10DyadicBlock21 parent.A = 0
  parent_B21_zero : p10DyadicBlock21 parent.B = 0
  child21_A : child21.A = p10DyadicBlock22 parent.A
  child21_B : child21.B = p10DyadicBlock11 parent.B
  child21_C : child21.C = p10DyadicBlock21 parent.C
  child21_exact :
    child21.exactSolution = p10DyadicBlock21 parent.exactSolution
  child11_A : child11.A = p10DyadicBlock11 parent.A
  child11_B : child11.B = p10DyadicBlock11 parent.B
  child22_A : child22.A = p10DyadicBlock22 parent.A
  child22_B : child22.B = p10DyadicBlock22 parent.B
  child12_A : child12.A = p10DyadicBlock11 parent.A
  child12_B : child12.B = p10DyadicBlock22 parent.B
  computed_21 :
    p10DyadicBlock21 parent.computedSolution = child21.computedSolution
  computed_11 :
    p10DyadicBlock11 parent.computedSolution = child11.computedSolution
  computed_22 :
    p10DyadicBlock22 parent.computedSolution = child22.computedSolution
  computed_12 :
    p10DyadicBlock12 parent.computedSolution = child12.computedSolution
  exact_block_21 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock21 parent.exactSolution) =
      -p10DyadicBlock21 parent.C
  exact_block_11 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock11 parent.B)
        (p10DyadicBlock11 parent.exactSolution) =
      -p10SylRExactRhs11 parent
  exact_block_22 :
    p10SylvesterAction
        (p10DyadicBlock22 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock22 parent.exactSolution) =
      -p10SylRExactRhs22 parent
  exact_block_12 :
    p10SylvesterAction
        (p10DyadicBlock11 parent.A) (p10DyadicBlock22 parent.B)
        (p10DyadicBlock12 parent.exactSolution) =
      -p10SylRExactRhs12 parent
  rhs11_first_order_error :
    p10DyadicFrobNorm (child11.C - p10SylRExactRhs11 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock11 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs22_first_order_error :
    p10DyadicFrobNorm (child22.C - p10SylRExactRhs22 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock22 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError21 parent child21 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock21 parent.exactSolution)
  rhs12_first_order_error :
    p10DyadicFrobNorm (child12.C - p10SylRExactRhs12 parent) ≤
      epsilon * p10DyadicFrobNorm (p10DyadicBlock12 parent.C) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10SylRBlockError11 parent child11 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.B) *
          p10DyadicFrobNorm (p10DyadicBlock11 parent.exactSolution) +
        p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10SylRBlockError22 parent child22 +
        muHalf * epsilon *
          p10DyadicFrobNorm (p10DyadicBlock12 parent.A) *
          p10DyadicFrobNorm (p10DyadicBlock22 parent.exactSolution)
  assembled_error_bound :
    p10SylRForwardError parent ≤
      p10SylRBlockError21 parent child21 +
        p10SylRBlockError11 parent child11 +
        p10SylRBlockError22 parent child22 +
        p10SylRBlockError12 parent child12
  child21_first_order_error :
    p10SylRBlockError21 parent child21 ≤ smallerError
  child11_first_order_error :
    p10SylRBlockError11 parent child11 ≤
      smallerError +
        (epsilon * globalCNorm + globalANorm * smallerError +
            muHalf * epsilon * globalANorm * globalRNorm) / globalSep
  child22_first_order_error :
    p10SylRBlockError22 parent child22 ≤
      smallerError +
        (epsilon * globalCNorm + globalBNorm * smallerError +
            muHalf * epsilon * globalBNorm * globalRNorm) / globalSep
  child12_first_order_error :
    p10SylRBlockError12 parent child12 ≤
      smallerError +
        (epsilon * globalCNorm +
            (globalANorm + globalBNorm) * smallerError +
            muHalf * epsilon * (globalANorm + globalBNorm) * globalRNorm) /
          globalSep

/-- Complete proof-carrying SylR recursion family for dimensions `2^k` up to
the requested depth. `errorEnvelope k` is the attained worst first-order error
among the dimension-`2^k` calls, including rounded right-hand sides. -/
structure P10SylRRun (depth : ℕ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  mu_mono : Monotone mu
  mu_ge_one : ∀ n, 0 < n → 1 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  Node : ℕ → Type
  top : Node depth
  problem : ∀ k, k ≤ depth → Node k → P10SylRProblem k
  errorEnvelope : ℕ → ℝ
  errorEnvelope_upper : ∀ k (hk : k ≤ depth) (node : Node k),
    p10SylRForwardError (problem k hk node) ≤ errorEnvelope k
  errorEnvelope_attained : ∀ k (hk : k ≤ depth),
    ∃ node : Node k,
      p10SylRForwardError (problem k hk node) = errorEnvelope k
  child21 : ∀ k, k < depth → Node (k + 1) → Node k
  child11 : ∀ k, k < depth → Node (k + 1) → Node k
  child22 : ∀ k, k < depth → Node (k + 1) → Node k
  child12 : ∀ k, k < depth → Node (k + 1) → Node k
  level : ∀ k (hk : k < depth) (node : Node (k + 1)),
    P10SylRLevelCertificate
      epsilon (mu (2 ^ (depth - 1))) (errorEnvelope k)
      (p10DyadicFrobNorm (problem depth le_rfl top).A)
      (p10DyadicFrobNorm (problem depth le_rfl top).B)
      (p10DyadicFrobNorm (problem depth le_rfl top).C)
      (p10DyadicFrobNorm (problem depth le_rfl top).exactSolution)
      (problem depth le_rfl top).separation.value
      (problem (k + 1) (Nat.succ_le_iff.mpr hk) node)
      (problem k (Nat.le_of_lt hk) (child21 k hk node))
      (problem k (Nat.le_of_lt hk) (child11 k hk node))
      (problem k (Nat.le_of_lt hk) (child22 k hk node))
      (problem k (Nat.le_of_lt hk) (child12 k hk node))
  node_A_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).A ≤
      p10DyadicFrobNorm (problem depth le_rfl top).A
  node_B_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).B ≤
      p10DyadicFrobNorm (problem depth le_rfl top).B
  node_R_norm_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    p10DyadicFrobNorm (problem k hk node).exactSolution ≤
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution
  node_sep_bound : ∀ k (hk : k ≤ depth) (node : Node k),
    (problem depth le_rfl top).separation.value ≤
      (problem k hk node).separation.value
  base_rounding_bound : errorEnvelope 0 ≤
    mu (2 ^ (depth - 1)) * epsilon *
      p10DyadicFrobNorm (problem depth le_rfl top).exactSolution *
      ((p10DyadicFrobNorm (problem depth le_rfl top).A +
          p10DyadicFrobNorm (problem depth le_rfl top).B) /
        (problem depth le_rfl top).separation.value)

noncomputable def p10SylRTopProblem {depth : ℕ}
    (run : P10SylRRun depth) : P10SylRProblem depth :=
  run.problem depth le_rfl run.top

noncomputable def p10SylRConditionRatio {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  (p10DyadicFrobNorm (p10SylRTopProblem run).A +
      p10DyadicFrobNorm (p10SylRTopProblem run).B) /
    (p10SylRTopProblem run).separation.value

noncomputable def p10SylRHalfMu {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.mu (2 ^ (depth - 1))

/-- Conventional first-order forward-error scale used in the comparison
following equation (20). -/
noncomputable def p10SylRConventionalForwardScale {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon * p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    p10SylRConditionRatio run

/-- Exact multiplier in the recurrence preceding equation (20). -/
noncomputable def p10SylRRecurrenceGrowth {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  4 + 2 * p10SylRConditionRatio run

/-- Exact first-order forcing term in the recurrence preceding (20). -/
noncomputable def p10SylRRecurrenceForcing {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  run.epsilon / (p10SylRTopProblem run).separation.value *
    (3 * p10DyadicFrobNorm (p10SylRTopProblem run).C +
      2 * p10SylRHalfMu run *
        (p10DyadicFrobNorm (p10SylRTopProblem run).A +
          p10DyadicFrobNorm (p10SylRTopProblem run).B) *
        p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution)

/-- Equation (20) with the explicit universal constant `2`; this is a finite
strengthening of the paper's unspecified big-O constant. -/
noncomputable def p10SylREquation20Bound {depth : ℕ}
    (run : P10SylRRun depth) : ℝ :=
  2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
    p10SylRHalfMu run * run.epsilon *
    p10DyadicFrobNorm (p10SylRTopProblem run).exactSolution *
    (p10SylRConditionRatio run) ^ (1 + Nat.log2 (2 ^ depth))

/-- Finite form of the recurrence, equation (20), its conventional-error
comparison, and the logarithmic condition-number exponent. -/
def P10SylRLogarithmicallyStable {depth : ℕ}
    (run : P10SylRRun depth) : Prop :=
  (∀ k, k < depth →
      run.errorEnvelope (k + 1) ≤
        p10SylRRecurrenceGrowth run * run.errorEnvelope k +
          p10SylRRecurrenceForcing run) ∧
    p10SylRForwardError (p10SylRTopProblem run) ≤
      p10SylREquation20Bound run ∧
    p10SylREquation20Bound run =
      2 * (((2 ^ depth : ℕ) : ℝ) ^ (1 + Real.logb 2 3)) *
        p10SylRHalfMu run * p10SylRConventionalForwardScale run *
        (p10SylRConditionRatio run) ^ Nat.log2 (2 ^ depth) ∧
    1 + Nat.log2 (2 ^ depth) = depth + 1

end HighamBench
