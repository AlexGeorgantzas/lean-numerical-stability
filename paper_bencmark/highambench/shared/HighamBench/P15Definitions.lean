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

/-- One scalar operation in the standard relative-error model (2.5). -/
def p15StandardRound (u exact rounded : ℝ) : Prop :=
  ∃ delta : ℝ, |delta| ≤ u ∧ rounded = exact * (1 + delta)

/-- The positive-precision regime inherited by Theorem 4.5. -/
def p15AdmissiblePrecision (c u epsilon : ℝ) : Prop :=
  0 < u ∧ 0 < epsilon ∧ u < epsilon ∧ 3 * c * u < 1

/-- A two-parameter scalar remainder is uniformly `O(u*epsilon)` as positive
`u` and `epsilon` tend to zero with `u < epsilon`. -/
def p15IsBigOMixedAtZero (remainder : ℝ → ℝ → ℝ) : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ u epsilon : ℝ,
      0 < u → 0 < epsilon → u < epsilon →
      u ≤ delta → epsilon ≤ delta →
      |remainder u epsilon| ≤ C * (u * epsilon)

/-- A scalar remainder is uniformly `O(u^2)` relative to the displayed
problem scale. This records the dimensionful convention used in (4.25). -/
def p15IsBigOSquareRelativeAtZero
    (remainder scale : ℝ → ℝ → ℝ) : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ u epsilon : ℝ,
      0 < u → 0 < epsilon → u < epsilon →
      u ≤ delta → epsilon ≤ delta → 0 ≤ scale u epsilon →
      |remainder u epsilon| ≤ C * u ^ 2 * scale u epsilon

/-- Section 2.1's relation between a dense matrix `A` and a BLR
representation `Atilde`. Off-diagonal ranks may differ from block to block and
are not identified with the later rank of the computed factors. -/
def p15BLRRepresents {p b : ℕ} (threshold : P15BLRThreshold)
    (epsilon : ℝ) (A Atilde : P15Matrix (p * b)) : Prop :=
  (∀ i : Fin p, p15MatrixBlock Atilde i i = p15MatrixBlock A i i) ∧
    ∀ i j : Fin p, i ≠ j →
      ∃ k : ℕ, ∃ X Y : P15RectMatrix b k,
        p15MatrixBlock Atilde i j = p15LowRankMatrix X Y ∧
          p15FrobNorm (p15MatrixBlock Atilde i j - p15MatrixBlock A i j) ≤
            epsilon *
              match threshold with
              | .local => p15FrobNorm (p15MatrixBlock A i j)
              | .global => p15FrobNorm A

/-- `r` is the least common off-diagonal rank bound of the computed factors,
which formalizes Section 4's maximum factor-rank convention. -/
def p15IsFactorBLRRank {p b : ℕ} (r : ℕ)
    (L U : P15Matrix (p * b)) : Prop :=
  p15IsBLRMatrix r L ∧ p15IsBLRMatrix r U ∧
    ∀ s : ℕ, p15IsBLRMatrix s L → p15IsBLRMatrix s U → r ≤ s

/-- Entrywise use of the relative-error model with one accumulated gamma
coefficient. -/
def p15EntrywiseStandardRound {m n : ℕ} (gamma : ℝ)
    (exact rounded : P15RectMatrix m n) : Prop :=
  ∀ i j, p15StandardRound gamma (exact i j) (rounded i j)

/-- One truncated-SVD compression in Assumption 2.1. -/
structure P15BlockCompression {b : ℕ} (epsilon beta : ℝ)
    (exact compressed : P15Matrix b) where
  error : P15Matrix b
  compressed_eq : compressed = exact + error
  error_le : p15FrobNorm error ≤ epsilon * beta

/-- The local or global unscaled threshold base attached to block `(i,k)`. -/
noncomputable def p15BLRCompressionBase {p b : ℕ}
    (threshold : P15BLRThreshold) (A : P15Matrix (p * b))
    (i k : Fin p) : ℝ :=
  match threshold with
  | .local => p15FrobNorm (p15MatrixBlock A i k)
  | .global => p15FrobNorm A

/-- The exact block update in lines 4 and 6 of Algorithms 1 and 2, including
the optional intermediate-recompression terms from Section 4.1.3. -/
noncomputable def p15BLRUpdatedBlock {p b : ℕ}
    (A L U : P15Matrix (p * b))
    (recompressionError : Fin p → Fin p → Fin p → P15Matrix b)
    (i k : Fin p) : P15Matrix b :=
  p15MatrixBlock A i k -
    ∑ j ∈ Finset.univ.filter (fun j : Fin p => j < k),
      (p15MatMul (p15MatrixBlock L i j) (p15MatrixBlock U j k) +
        recompressionError i k j)

/-- The recompression errors are absent in the `without` case and satisfy the
Section 4.1.3 threshold bound in the `with` case. -/
def p15RecompressionModel {p b : ℕ}
    (choice : P15BLRRecompression) (threshold : P15BLRThreshold)
    (epsilon : ℝ) (A : P15Matrix (p * b))
    (error : Fin p → Fin p → Fin p → P15Matrix b) : Prop :=
  match choice with
  | .without => ∀ i k j, error i k j = 0
  | .with => ∀ i k j, j < k →
      p15FrobNorm (error i k j) ≤
        epsilon * p15BLRCompressionBase threshold A i k

/-- A source-level execution of Algorithm 1. The exact update formulas feed
the factor step, and the off-diagonal factor blocks are compressed only after
they have been solved for. -/
structure P15CompletedUFCFactorization {p b : ℕ}
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  recompressionError : Fin p → Fin p → Fin p → P15Matrix b
  recompression_model :
    p15RecompressionModel recompression threshold epsilon A
      recompressionError
  updatedColumn : Fin p → Fin p → P15Matrix b
  updatedRow : Fin p → Fin p → P15Matrix b
  rawLower : Fin p → Fin p → P15Matrix b
  rawUpper : Fin p → Fin p → P15Matrix b
  lower_triangular : p15IsBlockLowerTriangular L
  upper_triangular : p15IsBlockUpperTriangular U
  update_column : ∀ k i, k ≤ i →
    p15EntrywiseStandardRound (p15GammaReal (p : ℝ) u)
      (p15BLRUpdatedBlock A L U recompressionError i k)
      (updatedColumn k i)
  update_row : ∀ k i, k ≤ i →
    p15EntrywiseStandardRound (p15GammaReal (p : ℝ) u)
      (p15BLRUpdatedBlock A L U recompressionError k i)
      (updatedRow k i)
  diagonal_updates_agree : ∀ k, updatedColumn k k = updatedRow k k
  diagonal_factor : ∀ k,
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (updatedColumn k k)
      (p15MatMul (p15MatrixBlock L k k) (p15MatrixBlock U k k))
  lower_solve : ∀ k i, k < i →
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (updatedColumn k i)
      (p15MatMul (rawLower i k) (p15MatrixBlock U k k))
  upper_solve : ∀ k i, k < i →
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (updatedRow k i)
      (p15MatMul (p15MatrixBlock L k k) (rawUpper k i))
  lower_diagonal_scale_pos : ∀ k, 0 < p15FrobNorm (p15MatrixBlock U k k)
  upper_diagonal_scale_pos : ∀ k, 0 < p15FrobNorm (p15MatrixBlock L k k)
  lower_compression : ∀ k i, k < i →
    P15BlockCompression epsilon
      (p15BLRCompressionBase threshold A i k /
        p15FrobNorm (p15MatrixBlock U k k))
      (rawLower i k) (p15MatrixBlock L i k)
  upper_compression : ∀ k i, k < i →
    P15BlockCompression epsilon
      (p15BLRCompressionBase threshold A k i /
        p15FrobNorm (p15MatrixBlock L k k))
      (rawUpper k i) (p15MatrixBlock U k i)

/-- A source-level execution of Algorithm 2. Updated off-diagonal blocks are
compressed before the factor solves, so the stored outputs come directly from
the factor step. -/
structure P15CompletedUCFFactorization {p b : ℕ}
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) where
  recompressionError : Fin p → Fin p → Fin p → P15Matrix b
  recompression_model :
    p15RecompressionModel recompression threshold epsilon A
      recompressionError
  updatedColumn : Fin p → Fin p → P15Matrix b
  updatedRow : Fin p → Fin p → P15Matrix b
  compressedColumn : Fin p → Fin p → P15Matrix b
  compressedRow : Fin p → Fin p → P15Matrix b
  lower_triangular : p15IsBlockLowerTriangular L
  upper_triangular : p15IsBlockUpperTriangular U
  update_column : ∀ k i, k ≤ i →
    p15EntrywiseStandardRound (p15GammaReal (p : ℝ) u)
      (p15BLRUpdatedBlock A L U recompressionError i k)
      (updatedColumn k i)
  update_row : ∀ k i, k ≤ i →
    p15EntrywiseStandardRound (p15GammaReal (p : ℝ) u)
      (p15BLRUpdatedBlock A L U recompressionError k i)
      (updatedRow k i)
  diagonal_updates_agree : ∀ k, updatedColumn k k = updatedRow k k
  lower_compression : ∀ k i, k < i →
    P15BlockCompression epsilon (p15BLRCompressionBase threshold A i k)
      (updatedColumn k i) (compressedColumn k i)
  upper_compression : ∀ k i, k < i →
    P15BlockCompression epsilon (p15BLRCompressionBase threshold A k i)
      (updatedRow k i) (compressedRow k i)
  diagonal_factor : ∀ k,
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (updatedColumn k k)
      (p15MatMul (p15MatrixBlock L k k) (p15MatrixBlock U k k))
  lower_solve : ∀ k i, k < i →
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (compressedColumn k i)
      (p15MatMul (p15MatrixBlock L i k) (p15MatrixBlock U k k))
  upper_solve : ∀ k i, k < i →
    p15EntrywiseStandardRound (p15GammaReal (b : ℝ) u)
      (compressedRow k i)
      (p15MatMul (p15MatrixBlock L k k) (p15MatrixBlock U k i))

/-- Completion of exactly one of the two algorithms named in Theorem 4.5. -/
def P15CompletedBLRFactorization {b p : ℕ}
    (algorithm : P15BLRFactorizationAlgorithm)
    (threshold : P15BLRThreshold) (recompression : P15BLRRecompression)
    (u epsilon : ℝ) (A L U : P15Matrix (p * b)) : Prop :=
  match algorithm with
  | .ufc => Nonempty
      (P15CompletedUFCFactorization threshold recompression u epsilon A L U)
  | .ucf => Nonempty
      (P15CompletedUCFFactorization threshold recompression u epsilon A L U)

/-- Forward or backward block-substitution order. -/
inductive P15TriangularSolveDirection where
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The exact right-hand side of one diagonal block solve after the already
computed block components have been subtracted. -/
noncomputable def p15TriangularResidual {p b : ℕ}
    (direction : P15TriangularSolveDirection)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b))
    (i : Fin p) (row : Fin b) : ℝ :=
  match direction with
  | .lower =>
      rhs (p15BlockIndex i row) -
        ∑ j ∈ Finset.univ.filter (fun j : Fin p => j < i),
          ∑ col : Fin b,
            p15MatrixBlock T i j row col * x (p15BlockIndex j col)
  | .upper =>
      rhs (p15BlockIndex i row) -
        ∑ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
          ∑ col : Fin b,
            p15MatrixBlock T i j row col * x (p15BlockIndex j col)

/-- A completed block triangular solve in the source order. Each diagonal
block equation is linked to the accumulated standard floating-point model;
the backward perturbations of Theorem 4.4 are not fields of this trace. -/
structure P15CompletedTriangularSolve {p b : ℕ}
    (direction : P15TriangularSolveDirection) (u : ℝ)
    (T : P15Matrix (p * b)) (rhs x : P15Vector (p * b)) : Prop where
  triangular :
    match direction with
    | .lower => p15IsBlockLowerTriangular T
    | .upper => p15IsBlockUpperTriangular T
  block_steps : ∀ i : Fin p, ∀ row : Fin b,
    p15StandardRound (p15GammaReal (p : ℝ) u)
      (p15TriangularResidual direction T rhs x i row)
      ((p15MatVec (p15MatrixBlock T i i) (fun col =>
        x (p15BlockIndex i col))) row)

/-- A precision family for the fixed input problem in Theorem 4.5. The trace
fields encode the two permitted algorithms and the ordered solves. The
component perturbation fields are the source-level interfaces supplied by
Theorems 4.2--4.4; aggregate system perturbations are deliberately absent and
are constructed by P15-T3. The factorization remainder is one uniform
two-parameter function, rather than a constant chosen after a run. -/
structure P15BLRLinearSolveFamily (b p r : ℕ) where
  block_size_pos : 0 < b
  block_count_pos : 0 < p
  rank_le_block_size : r ≤ b
  algorithm : P15BLRFactorizationAlgorithm
  threshold : P15BLRThreshold
  recompression : P15BLRRecompression
  A : P15Matrix (p * b)
  v : P15Vector (p * b)
  A_nonsingular : p15IsNonsingular A
  Atilde : ℝ → P15Matrix (p * b)
  L : ℝ → ℝ → P15Matrix (p * b)
  U : ℝ → ℝ → P15Matrix (p * b)
  yHat : ℝ → ℝ → P15Vector (p * b)
  xHat : ℝ → ℝ → P15Vector (p * b)
  represents : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15BLRRepresents threshold epsilon A (Atilde epsilon)
  factor_rank : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15IsFactorBLRRank r (L u epsilon) (U u epsilon)
  factorization_completed : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      P15CompletedBLRFactorization algorithm threshold recompression
        u epsilon (Atilde epsilon) (L u epsilon) (U u epsilon)
  factorError : ℝ → ℝ → P15Matrix (p * b)
  factorRemainder : ℝ → ℝ → ℝ
  factorization_eq : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      A + factorError u epsilon = p15MatMul (L u epsilon) (U u epsilon)
  factorError_le : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15FrobNorm (factorError u epsilon) ≤
        (p15BLRXi p threshold recompression * epsilon +
            p15GammaReal (p : ℝ) u) * p15FrobNorm A +
          p15GammaReal (p15BLRSolveCost b p r) u *
            p15FrobNorm (L u epsilon) * p15FrobNorm (U u epsilon) +
          factorRemainder u epsilon
  factorRemainder_nonneg : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      0 ≤ factorRemainder u epsilon
  factorRemainder_bigO : p15IsBigOMixedAtZero factorRemainder
  lowerError : ℝ → ℝ → P15Matrix (p * b)
  upperError : ℝ → ℝ → P15Matrix (p * b)
  lowerRhsError : ℝ → ℝ → P15Vector (p * b)
  upperRhsError : ℝ → ℝ → P15Vector (p * b)
  lower_completed : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      P15CompletedTriangularSolve .lower u (L u epsilon) v
        (yHat u epsilon)
  upper_completed : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      P15CompletedTriangularSolve .upper u (U u epsilon)
        (yHat u epsilon) (xHat u epsilon)
  lowerSolve_eq : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15MatVec (L u epsilon + lowerError u epsilon) (yHat u epsilon) =
        v + lowerRhsError u epsilon
  upperSolve_eq : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15MatVec (U u epsilon + upperError u epsilon) (xHat u epsilon) =
        yHat u epsilon + upperRhsError u epsilon
  lowerError_le : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15FrobNorm (lowerError u epsilon) ≤
        p15GammaReal (p15BLRSolveCost b p r) u *
          p15FrobNorm (L u epsilon)
  upperError_le : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15FrobNorm (upperError u epsilon) ≤
        p15GammaReal (p15BLRSolveCost b p r) u *
          p15FrobNorm (U u epsilon)
  lowerRhsError_le : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15VecNorm (lowerRhsError u epsilon) ≤
        p15GammaReal (p : ℝ) u * p15VecNorm v
  upperRhsError_le : ∀ u epsilon,
    p15AdmissiblePrecision (p15BLRSolveCost b p r) u epsilon →
      p15VecNorm (upperRhsError u epsilon) ≤
        p15GammaReal (p : ℝ) u * p15VecNorm (yHat u epsilon)

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
