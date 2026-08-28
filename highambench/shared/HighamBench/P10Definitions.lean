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

/-- The inherited-left error matrix produced to first order by multiplying
the left operand perturbation by the exact right operand. -/
noncomputable def p10InheritedLeftError {n : ℕ}
    (run : P10FirstOrderProductRun n) : P10Matrix n :=
  p10MatMul n run.leftPerturbation run.exactRight

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

/-- The selected inherited-right term. The first conjunct links all three
first-order matrices to the realized product error; the second gives equation
`(8)`'s `||A||*err(B,n)` bound for the middle matrix. -/
def P10InheritedRightEquation8Term {n : ℕ}
    (run : P10FirstOrderProductRun n) : Prop :=
  p10FirstOrderProductError run =
      run.localFirstOrderError +
        (p10InheritedRightError run + p10InheritedLeftError run) ∧
    run.matrixNorm.value (p10InheritedRightError run) ≤
      p10InheritedRightErrorContribution run

/-! ## Uniform stable-product model for equation (8) -/

/-- A positive machine precision. Quantifying over this type makes the
`O(epsilon^2)` term in the paper's first-order analysis uniform as epsilon
tends to zero through positive values. -/
abbrev P10PositiveEpsilon := {epsilon : ℝ // 0 < epsilon}

/-- One matrix-multiplication algorithm, with the norm and polynomially
bounded stability factor fixed across dimensions, inputs, and precisions. -/
structure P10StableMatrixMultiplication where
  matrixNorm : (n : ℕ) → P10ConsistentMatrixNorm n
  mu : ℕ → ℝ
  mu_nonneg : ∀ n, 0 ≤ mu n
  muDegree : ℕ
  muGrowthConstant : ℝ
  muGrowthConstant_nonneg : 0 ≤ muGrowthConstant
  mu_polynomial_bound : ∀ n, 0 < n →
    mu n ≤ muGrowthConstant * (n : ℝ) ^ muDegree
  product : (n : ℕ) → P10PositiveEpsilon →
    P10Matrix n → P10Matrix n → P10Matrix n

/-- An epsilon-indexed family of calls to one stable multiplication
algorithm. The local certificate is equation (1), after absorbing the
first-order change from perturbed operands into one uniform quadratic term.
The inherited errors themselves are required to be uniformly first order. -/
structure P10FirstOrderProductFamily
    (algorithm : P10StableMatrixMultiplication) (n : ℕ) where
  dimension_pos : 0 < n
  exactLeft : P10Matrix n
  exactRight : P10Matrix n
  leftPerturbation : P10PositiveEpsilon → P10Matrix n
  rightPerturbation : P10PositiveEpsilon → P10Matrix n
  leftInheritedError : P10PositiveEpsilon → ℝ
  rightInheritedError : P10PositiveEpsilon → ℝ
  leftInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ leftInheritedError epsilon
  rightInheritedError_nonneg : ∀ epsilon : P10PositiveEpsilon,
    0 ≤ rightInheritedError epsilon
  leftInheritedCoeff : ℝ
  rightInheritedCoeff : ℝ
  leftInheritedCoeff_nonneg : 0 ≤ leftInheritedCoeff
  rightInheritedCoeff_nonneg : 0 ≤ rightInheritedCoeff
  localSecondOrderCoeff : ℝ
  localSecondOrderCoeff_nonneg : 0 ≤ localSecondOrderCoeff
  radius : ℝ
  radius_pos : 0 < radius
  left_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (leftPerturbation epsilon) ≤
      leftInheritedError epsilon
  right_perturbation_bound : ∀ epsilon : P10PositiveEpsilon,
    (algorithm.matrixNorm n).value (rightPerturbation epsilon) ≤
      rightInheritedError epsilon
  left_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    leftInheritedError epsilon ≤ leftInheritedCoeff * (epsilon : ℝ)
  right_inherited_first_order : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    rightInheritedError epsilon ≤ rightInheritedCoeff * (epsilon : ℝ)
  local_error_bound : ∀ epsilon : P10PositiveEpsilon,
    (epsilon : ℝ) ≤ radius →
    (algorithm.matrixNorm n).value
        (algorithm.product n epsilon
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon) -
          p10MatMul n
            (exactLeft + leftPerturbation epsilon)
            (exactRight + rightPerturbation epsilon)) ≤
      algorithm.mu n * (epsilon : ℝ) *
          (algorithm.matrixNorm n).value exactLeft *
          (algorithm.matrixNorm n).value exactRight +
        localSecondOrderCoeff * (epsilon : ℝ) ^ 2

/-- The actual output of the fixed multiplication algorithm on the two
epsilon-dependent computed operands. -/
noncomputable def p10ProductFamilyComputed {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  algorithm.product n epsilon
    (family.exactLeft + family.leftPerturbation epsilon)
    (family.exactRight + family.rightPerturbation epsilon)

/-- The actual product error. No inherited cross term or local remainder is
removed from this quantity. -/
noncomputable def p10ProductFamilyError {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : P10Matrix n :=
  p10ProductFamilyComputed algorithm family epsilon -
    p10MatMul n family.exactLeft family.exactRight

/-- The three leading contributions printed in equation (8). -/
noncomputable def p10ProductFamilyErrorBudget {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n)
    (epsilon : P10PositiveEpsilon) : ℝ :=
  algorithm.mu n * (epsilon : ℝ) *
      (algorithm.matrixNorm n).value family.exactLeft *
      (algorithm.matrixNorm n).value family.exactRight +
    ((algorithm.matrixNorm n).value family.exactLeft *
        family.rightInheritedError epsilon +
      family.leftInheritedError epsilon *
        (algorithm.matrixNorm n).value family.exactRight)

/-! ## Exact multiplication-to-inversion reduction -/

/-- A three-by-three block matrix whose entries are square real matrices. This
is the block level of the unnumbered display in the proof of Theorem 3.3. -/
abbrev P10ThreeBlockMatrix (n : ℕ) :=
  Matrix (Fin 3) (Fin 3) (P10Matrix n)

/-- The unit upper-triangular block matrix built from the two matrices whose
product is to be recovered by one exact inversion. -/
noncomputable def p10MultiplicationReductionInput {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), A, 0;
     0, 1, B;
     0, 0, 1]

/-- The inverse displayed in the proof of Theorem 3.3. Its upper-right block
is the desired product A times B. -/
noncomputable def p10MultiplicationReductionInverse {n : ℕ}
    (A B : P10Matrix n) : P10ThreeBlockMatrix n :=
  !![(1 : P10Matrix n), -A, p10MatMul n A B;
     0, 1, -B;
     0, 0, 1]

/-- Block multiplication for the three-by-three reduction matrices. -/
noncomputable def p10ThreeBlockMul {n : ℕ}
    (X Y : P10ThreeBlockMatrix n) : P10ThreeBlockMatrix n :=
  X * Y

/-- Identity at the three-by-three block level. -/
noncomputable def p10ThreeBlockIdentity (n : ℕ) : P10ThreeBlockMatrix n :=
  1

/-- Exact finite content of the converse reduction in Theorem 3.3: the
printed candidate is a two-sided inverse and its (0,2) block is A times B. -/
def P10MultiplicationViaInverse {n : ℕ} (A B : P10Matrix n) : Prop :=
  p10ThreeBlockMul (p10MultiplicationReductionInput A B)
      (p10MultiplicationReductionInverse A B) =
      p10ThreeBlockIdentity n ∧
    p10ThreeBlockMul (p10MultiplicationReductionInverse A B)
      (p10MultiplicationReductionInput A B) =
      p10ThreeBlockIdentity n ∧
    p10MultiplicationReductionInverse A B (0 : Fin 3) (2 : Fin 3) =
      p10MatMul n A B

end HighamBench
