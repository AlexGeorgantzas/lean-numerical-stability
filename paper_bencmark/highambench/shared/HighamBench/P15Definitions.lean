import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P15 definitions

Paper-scoped finite matrix notation for Higham and Mary's analysis of block
low-rank LU factorization and triangular solves.
-/

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-- A finite square real matrix in the P15 model. -/
abbrev P15Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- A finite rectangular real matrix in the P15 model. -/
abbrev P15RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- A finite real vector in the P15 model. -/
abbrev P15Vector (n : ℕ) := Fin n → ℝ

/-- Exact multiplication of compatible finite rectangular matrices. -/
noncomputable def p15RectMatMul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    P15RectMatrix m p :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Exact finite matrix multiplication. -/
noncomputable def p15MatMul {n : ℕ} (A B : P15Matrix n) : P15Matrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

/-- Exact finite matrix-vector multiplication. -/
noncomputable def p15MatVec {n : ℕ} (A : P15Matrix n)
    (x : P15Vector n) : P15Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The paper's unsquared, unnormalized Frobenius norm for a rectangular
matrix, written explicitly as `sqrt (sum_i sum_j A_ij^2)`. -/
noncomputable def p15RectFrobNorm {m n : ℕ}
    (A : P15RectMatrix m n) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

/-- Square specialization of the Frobenius norm used throughout P15. -/
noncomputable def p15FrobNorm {n : ℕ} (A : P15Matrix n) : ℝ :=
  p15RectFrobNorm A

/-- Exact transpose of a finite rectangular matrix. -/
def p15RectTranspose {m n : ℕ} (A : P15RectMatrix m n) :
    P15RectMatrix n m :=
  fun j i ↦ A i j

/-- Exact action of a finite rectangular matrix on a vector. -/
noncomputable def p15RectMatVec {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

/-- The low-rank matrix `Atilde = X Y^T` in Lemma 3.1. -/
noncomputable def p15LowRankMatrix {b r : ℕ}
    (X Y : P15RectMatrix b r) : P15Matrix b :=
  p15RectMatMul X (p15RectTranspose Y)

/-- Column orthonormality `X^T X = I` in the real finite model. -/
def p15OrthonormalColumns {b r : ℕ} (X : P15RectMatrix b r) : Prop :=
  ∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0

/-- The paper's real-index gamma function `gamma_k = ku/(1-ku)`. -/
noncomputable def p15GammaReal (k u : ℝ) : ℝ :=
  k * u / (1 - k * u)

/-- The operation-count index `c = b + r^(3/2)` from Lemma 3.1. For a
nonnegative integer rank, `r^(3/2) = r * sqrt r`. -/
noncomputable def p15LowRankKernelCost (b r : ℕ) : ℝ :=
  (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)

/-- A proof-carrying finite execution of the ordered computation
`wHat = fl(Y^T v)` followed by `zHat = fl(X wHat)` in Lemma 3.1. The stage
perturbation fields are the standard matrix-vector backward-error interface
recalled in Lemma 2.1; the aggregate perturbations in (3.1) and (3.2) are not
assumed here. -/
structure P15LowRankMatVecExecution (b r : ℕ) where
  A : P15Matrix b
  X : P15RectMatrix b r
  Y : P15RectMatrix b r
  v : P15Vector b
  epsilon : ℝ
  beta : ℝ
  unitRoundoff : ℝ
  epsilon_pos : 0 < epsilon
  beta_pos : 0 < beta
  unitRoundoff_pos : 0 < unitRoundoff
  unitRoundoff_lt_epsilon : unitRoundoff < epsilon
  gamma_valid :
    p15LowRankKernelCost b r * unitRoundoff < 1
  x_orthonormal : p15OrthonormalColumns X
  truncError : P15Matrix b
  approximation_eq : p15LowRankMatrix X Y = A + truncError
  truncError_le : p15FrobNorm truncError ≤ epsilon * beta
  wHat : P15Vector r
  zHat : P15Vector b
  deltaY : P15RectMatrix b r
  deltaX : P15RectMatrix b r
  first_stage_eq :
    wHat = p15RectMatVec (p15RectTranspose (Y + deltaY)) v
  first_stage_error_le :
    p15RectFrobNorm deltaY ≤
      p15GammaReal (b : ℝ) unitRoundoff * p15RectFrobNorm Y
  second_stage_eq :
    zHat = p15RectMatVec (X + deltaX) wHat
  second_stage_error_le :
    p15RectFrobNorm deltaX ≤
      p15GammaReal (r : ℝ) unitRoundoff * p15RectFrobNorm X

/-- The explicit low-rank floating-point perturbation obtained by expanding
`(X + deltaX)(Y + deltaY)^T`. -/
noncomputable def p15LowRankRoundingError {b r : ℕ}
    (run : P15LowRankMatVecExecution b r) : P15Matrix b :=
  p15RectMatMul run.X (p15RectTranspose run.deltaY) +
    p15RectMatMul run.deltaX (p15RectTranspose run.Y) +
    p15RectMatMul run.deltaX (p15RectTranspose run.deltaY)

/-- The equation (3.2) perturbation: low-rank truncation plus the equation
(3.1) floating-point perturbation. -/
noncomputable def p15LowRankTotalError {b r : ℕ}
    (run : P15LowRankMatVecExecution b r) : P15Matrix b :=
  run.truncError + p15LowRankRoundingError run

/-- Euclidean vector norm used for the right-hand-side estimate in Theorem 4.5. -/
noncomputable def p15VecNorm {n : ℕ} (x : P15Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- The two BLR LU factorization orders covered by Theorem 4.5. -/
inductive P15BLRFactorizationAlgorithm where
  | ufc
  | ucf
  deriving DecidableEq, Repr

/-- The local and global low-rank threshold choices in Table 1. -/
inductive P15BLRThreshold where
  | local
  | global
  deriving DecidableEq, Repr

/-- Whether the factorization performs the intermediate recompressions from
Section 4.1.3. -/
inductive P15BLRRecompression where
  | without
  | with
  deriving DecidableEq, Repr

/-- The four exact values of `xi_p` in Table 1. -/
noncomputable def p15BLRXi (p : ℕ) (threshold : P15BLRThreshold)
    (recompression : P15BLRRecompression) : ℝ :=
  match recompression, threshold with
  | .without, .local => 1
  | .without, .global => p
  | .with, .local => p
  | .with, .global => (p : ℝ) ^ 2 / Real.sqrt 6

/-- The common operation-count index `c = b + 2*r^(3/2) + p` in Theorem
4.5. -/
noncomputable def p15BLRSolveCost (b p r : ℕ) : ℝ :=
  (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)

/-- Flatten a block-row and within-block row into an index of a `p*b` matrix. -/
def p15BlockIndex {p b : ℕ} (i : Fin p) (row : Fin b) : Fin (p * b) :=
  ⟨i.1 * b + row.1, by
    have hi : i.1 + 1 ≤ p := Nat.succ_le_iff.mpr i.2
    have hblock : (i.1 + 1) * b ≤ p * b := Nat.mul_le_mul_right b hi
    have hrow : i.1 * b + row.1 < (i.1 + 1) * b := by
      simpa [Nat.add_mul] using Nat.add_lt_add_left row.2 (i.1 * b)
    exact lt_of_lt_of_le hrow hblock⟩

/-- Extract one `b`-by-`b` block from a matrix of order `p*b`. -/
def p15MatrixBlock {p b : ℕ} (A : P15Matrix (p * b))
    (i j : Fin p) : P15Matrix b :=
  fun row col => A (p15BlockIndex i row) (p15BlockIndex j col)

/-- A `p*b` matrix whose off-diagonal blocks have rank at most `r`, represented
by uniformly padded `b`-by-`r` factors. -/
def p15IsBLRMatrix {p b : ℕ} (r : ℕ) (A : P15Matrix (p * b)) : Prop :=
  ∃ X Y : Fin p → Fin p → P15RectMatrix b r,
    ∀ i j, i ≠ j →
      p15MatrixBlock A i j = p15LowRankMatrix (X i j) (Y i j)

/-- Block lower-triangular shape. -/
def p15IsBlockLowerTriangular {p b : ℕ} (L : P15Matrix (p * b)) : Prop :=
  ∀ i j : Fin p, i < j → p15MatrixBlock L i j = 0

/-- Block upper-triangular shape. -/
def p15IsBlockUpperTriangular {p b : ℕ} (U : P15Matrix (p * b)) : Prop :=
  ∀ i j : Fin p, j < i → p15MatrixBlock U i j = 0

/-- Exact identity matrix in the P15 finite model. -/
def p15Identity (n : ℕ) : P15Matrix n :=
  fun i j => if i = j then 1 else 0

/-- Two-sided nonsingularity certificate for the input matrix. -/
def p15IsNonsingular {n : ℕ} (A : P15Matrix n) : Prop :=
  ∃ Ainv : P15Matrix n,
    p15MatMul Ainv A = p15Identity n ∧
      p15MatMul A Ainv = p15Identity n

/-- A proof-carrying real-valued execution of the complete computation in
Theorem 4.5. A value records a completed UFC or UCF factorization and the two
ordered BLR triangular solves. The fields are the exact finite conclusions of
Theorems 4.2--4.4, with every coefficient tied to `b`, `p`, `r`, `u`, the
threshold case, and the recompression case. Exceptional floating-point values
are outside this standard-model trace. -/
structure P15BLRLinearSolveExecution (b p r : ℕ) where
  block_size_pos : 0 < b
  block_count_pos : 0 < p
  rank_le_block_size : r ≤ b
  algorithm : P15BLRFactorizationAlgorithm
  threshold : P15BLRThreshold
  recompression : P15BLRRecompression
  A : P15Matrix (p * b)
  L : P15Matrix (p * b)
  U : P15Matrix (p * b)
  v : P15Vector (p * b)
  A_nonsingular : p15IsNonsingular A
  A_is_blr : p15IsBLRMatrix r A
  L_is_blr : p15IsBLRMatrix r L
  U_is_blr : p15IsBLRMatrix r U
  L_lower_triangular : p15IsBlockLowerTriangular L
  U_upper_triangular : p15IsBlockUpperTriangular U
  epsilon : ℝ
  unitRoundoff : ℝ
  epsilon_pos : 0 < epsilon
  unitRoundoff_pos : 0 < unitRoundoff
  unitRoundoff_lt_epsilon : unitRoundoff < epsilon
  gamma_valid :
    3 * p15BLRSolveCost b p r * unitRoundoff < 1
  factorCoreError : P15Matrix (p * b)
  factorMixedError : P15Matrix (p * b)
  factorError : P15Matrix (p * b)
  factorError_eq : factorError = factorCoreError + factorMixedError
  factorization_eq : p15MatMul L U = A + factorError
  factorCoreError_le :
    p15FrobNorm factorCoreError ≤
      (p15BLRXi p threshold recompression * epsilon +
          p15GammaReal (p : ℝ) unitRoundoff) * p15FrobNorm A +
        p15GammaReal (p15BLRSolveCost b p r) unitRoundoff *
          p15FrobNorm L * p15FrobNorm U
  factorMixedConstant : ℝ
  factorMixedConstant_nonneg : 0 ≤ factorMixedConstant
  factorMixedError_le :
    p15FrobNorm factorMixedError ≤
      factorMixedConstant * unitRoundoff * epsilon
  yHat : P15Vector (p * b)
  xHat : P15Vector (p * b)
  lowerError : P15Matrix (p * b)
  upperError : P15Matrix (p * b)
  lowerRhsError : P15Vector (p * b)
  upperRhsError : P15Vector (p * b)
  lowerSolve_eq :
    p15MatVec (L + lowerError) yHat = v + lowerRhsError
  upperSolve_eq :
    p15MatVec (U + upperError) xHat = yHat + upperRhsError
  lowerError_le :
    p15FrobNorm lowerError ≤
      p15GammaReal (p15BLRSolveCost b p r) unitRoundoff * p15FrobNorm L
  upperError_le :
    p15FrobNorm upperError ≤
      p15GammaReal (p15BLRSolveCost b p r) unitRoundoff * p15FrobNorm U
  lowerRhsError_le :
    p15VecNorm lowerRhsError ≤
      p15GammaReal (p : ℝ) unitRoundoff * p15VecNorm v
  upperRhsError_le :
    p15VecNorm upperRhsError ≤
      p15GammaReal (p : ℝ) unitRoundoff * p15VecNorm yHat

/-- Exact matrix perturbation obtained by composing a perturbed factorization
with perturbed forward and backward substitutions. -/
noncomputable def p15ComposedMatrixError {n : ℕ}
    (factorError lowerError upperError L U : P15Matrix n) : P15Matrix n :=
  factorError + p15MatMul lowerError U +
    p15MatMul L upperError + p15MatMul lowerError upperError

/-- Exact right-hand-side perturbation obtained by composing the two
triangular solves. -/
noncomputable def p15ComposedRhsError {n : ℕ}
    (rhsLower rhsUpper : P15Vector n)
    (L lowerError : P15Matrix n) : P15Vector n :=
  rhsLower + p15MatVec L rhsUpper + p15MatVec lowerError rhsUpper

end HighamBench
