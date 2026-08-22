import HighamBench.Core
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

namespace HighamBench

/-- Square real matrices used for the finite P11 certificates. -/
abbrev P11Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Rectangular real matrices used by the P11 CGS-P execution model. -/
abbrev P11RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Matrix multiplication in the P11 setting. -/
noncomputable def p11MatMul (n : ℕ) (A B : P11Matrix n) : P11Matrix n :=
  A * B

/-- Matrix transpose in the P11 setting. -/
def p11Transpose {n : ℕ} (A : P11Matrix n) : P11Matrix n :=
  A.transpose

/-- The identity matrix. -/
def p11Identity (n : ℕ) : P11Matrix n :=
  1

/-- Explicit Frobenius norm for the condition-neutral public statements. -/
noncomputable def p11FrobNorm {n : ℕ} (A : P11Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

/-- Explicit Euclidean norm for a finite real vector. -/
noncomputable def p11VecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

/-- Matrix-vector multiplication. -/
noncomputable def p11MatVec {n : ℕ} (A : P11Matrix n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  A.mulVec x

/-- The first valid column index of a nonempty finite matrix. -/
def p11FirstIndex {n : ℕ} (hn : 0 < n) : Fin n :=
  ⟨0, hn⟩

/-- The leading `(k+1) x (k+1)` block of a square matrix. -/
def p11LeadingBlock {n : ℕ} (R : P11Matrix n) (k : Fin n) :
    P11Matrix (k.val + 1) :=
  fun i j =>
    R (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) i)
      (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) j)

/-- The first `k+1` columns of a rectangular matrix. A `Fin n` index is
zero-based and therefore represents the paper's positive prefix index `k+1`. -/
def p11ColumnPrefix {m n : ℕ} (A : P11RectMatrix m n) (k : Fin n) :
    P11RectMatrix m (k.val + 1) :=
  fun i j => A i (Fin.castLE (Nat.succ_le_iff.mpr k.isLt) j)

/-- Exact induced spectral 2-norm used in P11. -/
noncomputable def p11OpNorm2 {n : ℕ} (A : P11Matrix n) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- Exact rectangular spectral 2-norm used for the prefixes in Theorem 1. -/
noncomputable def p11RectOpNorm2 {m n : ℕ}
    (A : P11RectMatrix m n) : ℝ :=
  @norm (Matrix (Fin m) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- The paper's first residual coefficient `c1(m,k)`. -/
noncomputable def p11C1 (m k : ℕ) : ℝ :=
  if k = 1 then 1
  else
    2 * Real.sqrt (2 * (m : ℝ) * (k : ℝ)) +
      2 * Real.sqrt (k : ℝ)

/-- The paper's normal-equations coefficient `c2(m,k)`. -/
noncomputable def p11C2 (m k : ℕ) : ℝ :=
  if k = 1 then (m : ℝ) + 2
  else
    ((7 : ℝ) / 2) * (m : ℝ) * (k : ℝ) ^ 2 -
      ((3 : ℝ) / 2) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ)

/-- The paper's condition-(3) coefficient `c4 = c2 + 2*c1`. -/
noncomputable def p11C4 (m k : ℕ) : ℝ :=
  p11C2 m k + 2 * p11C1 m k

/-- The paper's norm-comparison coefficient `c3 = c2/2`. -/
noncomputable def p11C3 (m k : ℕ) : ℝ :=
  (1 / 2 : ℝ) * p11C2 m k

/-- Exact spectral condition number represented by a matrix and certified inverse. -/
noncomputable def p11Kappa2 {n : ℕ} (R Rinv : P11Matrix n) : ℝ :=
  p11OpNorm2 R * p11OpNorm2 Rinv

/-- The normalized finite part of the IEEE arithmetic used by Algorithm 2's
first-column initialization. The computed norm carries the paper's explicit
first-order error with its unspecified `O(epsilonM^2)` coefficient. A scalar
division exposes only its primitive relative error; it does not supply the
matrix witness that equation (16) is meant to produce. -/
structure P11NormalizedIEEEArithmetic (epsilonM : ℝ) where
  normalized : ℝ → Prop
  divide : ℝ → ℝ → ℝ
  computedNorm : ∀ {m : ℕ}, (Fin m → ℝ) → ℝ
  normSecondOrderCoeff : ℕ → ℝ
  norm_second_order_nonneg : ∀ m, 0 ≤ normSecondOrderCoeff m
  computed_norm_error : ∀ {m : ℕ} (a : Fin m → ℝ),
    ∃ delta : ℝ,
      computedNorm a = p11VecNorm a * (1 + delta) ∧
        |delta| ≤ ((1 / 2 : ℝ) * (m : ℝ) + 1) * epsilonM +
          normSecondOrderCoeff m * epsilonM ^ 2
  computed_norm_nonneg : ∀ {m : ℕ} (a : Fin m → ℝ),
    0 ≤ computedNorm a
  divide_normalized : ∀ x denominator,
    denominator ≠ 0 → normalized (x / denominator) →
      ∃ delta : ℝ,
        |delta| ≤ epsilonM ∧
          divide x denominator = (x / denominator) * (1 + delta)

/-- Proof-carrying execution contract for the first column of CGS-P under the
standing hypotheses of Theorem 1. Real-valued error equations represent only
the normalized finite regime assumed by the paper. -/
structure P11CGSPFirstColumnRun (m n : ℕ) where
  row_dimension_pos : 0 < m
  column_dimension_pos : 0 < n
  columns_le_rows : n ≤ m
  A : P11RectMatrix m n
  Q : P11RectMatrix m n
  R : P11Matrix n
  full_column_rank : Function.Injective A.mulVec
  R_upper_triangular : ∀ i j : Fin n, j.val < i.val → R i j = 0
  epsilonM : ℝ
  epsilonM_pos : 0 < epsilonM
  epsilonM_lt_one : epsilonM < 1
  arithmetic : P11NormalizedIEEEArithmetic epsilonM
  leadingInverse : ∀ k : Fin n, P11Matrix (k.val + 1)
  leading_left_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (leadingInverse k) (p11LeadingBlock R k) =
      p11Identity (k.val + 1)
  leading_right_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (p11LeadingBlock R k) (leadingInverse k) =
      p11Identity (k.val + 1)
  condition_3 : ∀ k : Fin n,
    p11C4 m (k.val + 1) * epsilonM *
        p11Kappa2 (p11LeadingBlock R k) (leadingInverse k) ^ 2 < 1
  first_norm_computed :
    R (p11FirstIndex column_dimension_pos)
        (p11FirstIndex column_dimension_pos) =
      arithmetic.computedNorm
        (fun i => A i (p11FirstIndex column_dimension_pos))
  first_division_normalized : ∀ i : Fin m,
    arithmetic.normalized
      (A i (p11FirstIndex column_dimension_pos) /
        R (p11FirstIndex column_dimension_pos)
          (p11FirstIndex column_dimension_pos))
  first_division_computed : ∀ i : Fin m,
    Q i (p11FirstIndex column_dimension_pos) =
      arithmetic.divide
        (A i (p11FirstIndex column_dimension_pos))
        (R (p11FirstIndex column_dimension_pos)
          (p11FirstIndex column_dimension_pos))

/-- The one-column input matrix `A1`. -/
def p11A1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11RectMatrix m 1 :=
  fun i _ => run.A i (p11FirstIndex run.column_dimension_pos)

/-- The one-column computed matrix `Q1`. -/
def p11Q1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11RectMatrix m 1 :=
  fun i _ => run.Q i (p11FirstIndex run.column_dimension_pos)

/-- The one-by-one computed leading factor `R1`. -/
def p11R1 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) :
    P11Matrix 1 :=
  fun _ _ => run.R (p11FirstIndex run.column_dimension_pos)
    (p11FirstIndex run.column_dimension_pos)

/-- Rectangular matrix multiplication for the P11 first-column residual. -/
noncomputable def p11RectMatMul {m n p : ℕ}
    (A : P11RectMatrix m n) (B : P11RectMatrix n p) : P11RectMatrix m p :=
  A * B

/-- The exact post-analysis one-column residual `A1 - Q1*R1`. -/
noncomputable def p11FirstColumnFactorizationResidual {m n : ℕ}
    (run : P11CGSPFirstColumnRun m n) : P11RectMatrix m 1 :=
  p11A1 run - p11RectMatMul (p11Q1 run) (p11R1 run)

/-- The exact vector residual `a1 - q1*r11`. -/
noncomputable def p11FirstColumnResidualVector {m n : ℕ}
    (run : P11CGSPFirstColumnRun m n) : Fin m → ℝ :=
  fun i =>
    run.A i (p11FirstIndex run.column_dimension_pos) -
      run.Q i (p11FirstIndex run.column_dimension_pos) *
        run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos)

/-- The spectral 2-norm of a one-column matrix, exactly its column's Euclidean norm. -/
noncomputable def p11FirstColumnMatrixNorm2 {m : ℕ}
    (A : P11RectMatrix m 1) : ℝ :=
  p11VecNorm (fun i => A i 0)

/-- The computed-norm relation, exact first-column residual identity, and
complete norm chain in equation (16), for one produced witness `G1`. -/
structure P11Equation16Witness {m n : ℕ}
    (run : P11CGSPFirstColumnRun m n) (G1 : P11Matrix m) : Prop where
  denominator_pos :
    0 < run.R (p11FirstIndex run.column_dimension_pos)
      (p11FirstIndex run.column_dimension_pos)
  norm_roundoff_relation : ∃ delta : ℝ,
    run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos) =
        p11VecNorm
            (fun i => run.A i (p11FirstIndex run.column_dimension_pos)) *
          (1 + delta) ∧
      |delta| ≤ ((1 / 2 : ℝ) * (m : ℝ) + 1) * run.epsilonM +
        run.arithmetic.normSecondOrderCoeff m * run.epsilonM ^ 2
  normalization_relation : ∀ i : Fin m,
    run.Q i (p11FirstIndex run.column_dimension_pos) =
      (run.A i (p11FirstIndex run.column_dimension_pos) +
          p11MatVec G1
            (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i) /
        run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos)
  perturbation_opNorm_bound :
    p11OpNorm2 G1 ≤ run.epsilonM
  factorization_residual_identity :
    p11FirstColumnFactorizationResidual run =
      fun i _ => p11FirstColumnResidualVector run i
  residual_action_identity :
    p11FirstColumnResidualVector run =
      fun i =>
        -p11MatVec G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i
  matrix_vector_norm_identity :
    p11FirstColumnMatrixNorm2 (p11FirstColumnFactorizationResidual run) =
      p11VecNorm (p11FirstColumnResidualVector run)
  residual_action_norm_identity :
    p11VecNorm (p11FirstColumnResidualVector run) =
      p11VecNorm
        (p11MatVec G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)))
  operator_action_bound :
    p11VecNorm
        (p11MatVec G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos))) ≤
      p11OpNorm2 G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))
  machine_unit_bound :
    p11OpNorm2 G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) ≤
      run.epsilonM *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))

/-- The source's witness-producing first-column claim. -/
def P11Equation16 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) : Prop :=
  ∃ G1 : P11Matrix m, P11Equation16Witness run G1

/-- The loss-of-orthogonality matrix appearing in Theorem 1(7). -/
noncomputable def p11OrthogonalityDefect {n : ℕ}
    (Q : P11Matrix n) : P11Matrix n :=
  p11Identity n - p11MatMul n (p11Transpose Q) Q

/-- The normal-equations residual in Theorem 1(5). -/
noncomputable def p11NormalEquationResidual {n : ℕ}
    (A R : P11Matrix n) : P11Matrix n :=
  p11MatMul n (p11Transpose R) R -
    p11MatMul n (p11Transpose A) A

/-- The exact inner residual in the appendix derivation of Theorem 1(7). -/
noncomputable def p11DefectCore {n : ℕ}
    (A dA R : P11Matrix n) : P11Matrix n :=
  p11NormalEquationResidual A R -
    p11MatMul n (p11Transpose A) dA -
    p11MatMul n (p11Transpose dA) A -
    p11MatMul n (p11Transpose dA) dA

/-- Transpose of a rectangular P11 matrix. -/
def p11RectTranspose {m n : ℕ}
    (A : P11RectMatrix m n) : P11RectMatrix n m :=
  A.transpose

/-- The rectangular loss-of-orthogonality matrix `I - Q^T Q`. -/
noncomputable def p11RectOrthogonalityDefect {m k : ℕ}
    (Q : P11RectMatrix m k) : P11Matrix k :=
  p11Identity k - p11RectMatMul (p11RectTranspose Q) Q

/-- The rectangular normal-equations residual `R^T R - A^T A`. -/
noncomputable def p11RectNormalEquationResidual {m k : ℕ}
    (A : P11RectMatrix m k) (R : P11Matrix k) : P11Matrix k :=
  p11MatMul k (p11Transpose R) R -
    p11RectMatMul (p11RectTranspose A) A

/-- The exact rectangular inner residual in the derivation of Theorem 1(7). -/
noncomputable def p11RectDefectCore {m k : ℕ}
    (A dA : P11RectMatrix m k) (R : P11Matrix k) : P11Matrix k :=
  p11RectNormalEquationResidual A R -
    p11RectMatMul (p11RectTranspose A) dA -
    p11RectMatMul (p11RectTranspose dA) A -
    p11RectMatMul (p11RectTranspose dA) dA

/-- Exact Euclidean norm of one input column in Algorithm 2. -/
noncomputable def p11CGSPColumnNorm {m n : ℕ}
    (A : P11RectMatrix m n) (k : Fin n) : ℝ :=
  p11VecNorm fun i ↦ A i k

/-- Values with indices before `k`, extended by zero to the full column set. -/
def p11EarlierVector {n : ℕ} (k : Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ if j.val < k.val then x j else 0

/-- A normalized finite arithmetic interface for the operations that appear in
Algorithm 2. Dot products expose componentwise accumulated relative errors;
the scalar operations use the paper's normalized-range relative-error law. -/
structure P11CGSPNormalizedArithmetic (epsilonM : ℝ)
    extends P11NormalizedIEEEArithmetic epsilonM where
  add : ℝ → ℝ → ℝ
  subtract : ℝ → ℝ → ℝ
  multiply : ℝ → ℝ → ℝ
  squareRoot : ℝ → ℝ
  dot : ∀ {dimension : ℕ}, (Fin dimension → ℝ) → (Fin dimension → ℝ) → ℝ
  add_normalized : ∀ x y, normalized (x + y) →
    ∃ delta : ℝ, |delta| ≤ epsilonM ∧ add x y = (x + y) * (1 + delta)
  subtract_normalized : ∀ x y, normalized (x - y) →
    ∃ delta : ℝ, |delta| ≤ epsilonM ∧ subtract x y = (x - y) * (1 + delta)
  multiply_normalized : ∀ x y, normalized (x * y) →
    ∃ delta : ℝ, |delta| ≤ epsilonM ∧ multiply x y = (x * y) * (1 + delta)
  square_root_normalized : ∀ x, 0 ≤ x → normalized (Real.sqrt x) →
    ∃ delta : ℝ,
      |delta| ≤ epsilonM ∧ squareRoot x = Real.sqrt x * (1 + delta)
  dot_error : ∀ {dimension : ℕ} (x y : Fin dimension → ℝ),
    ∃ theta : Fin dimension → ℝ,
      (∀ i, |theta i| ≤ (dimension : ℝ) * epsilonM) ∧
        dot x y = ∑ i, x i * y i * (1 + theta i)

/-- One column of a successful normalized-range execution of Algorithm 2.
Every stored output is linked to the corresponding arithmetic operation; no
factorization, normal-equation, or orthogonality estimate is stored here. -/
structure P11CGSPColumnTrace {m n : ℕ}
    (arithmetic : P11CGSPNormalizedArithmetic epsilonM)
    (A Q : P11RectMatrix m n) (R : P11Matrix n) (k : Fin n) where
  s : Fin n → ℝ
  v : Fin m → ℝ
  psi : ℝ
  phi : ℝ
  projection_support : ∀ j : Fin n, k.val ≤ j.val → s j = 0
  first_diagonal_relation : k.val = 0 →
    R k k = arithmetic.computedNorm (fun i ↦ A i k)
  first_division_normalized : k.val = 0 → ∀ i : Fin m,
    arithmetic.normalized (A i k / R k k)
  first_normalization_relation : k.val = 0 → ∀ i : Fin m,
    Q i k = arithmetic.divide (A i k) (R k k)
  later_projection_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val →
      s j = arithmetic.dot (fun i ↦ Q i j) (fun i ↦ A i k)
  later_upper_factor_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val → R j k = s j
  later_residual_relation : 0 < k.val → ∀ i : Fin m,
    v i = arithmetic.subtract (A i k)
      (arithmetic.dot (fun j ↦ Q i j) (p11EarlierVector k s))
  later_psi_relation : 0 < k.val →
    psi = arithmetic.computedNorm (fun i ↦ A i k)
  later_phi_relation : 0 < k.val →
    phi = arithmetic.computedNorm (p11EarlierVector k s)
  later_pythagorean_domain : 0 < k.val →
    0 ≤ arithmetic.subtract psi phi
  later_diagonal_relation : 0 < k.val →
    R k k = arithmetic.multiply
      (arithmetic.squareRoot (arithmetic.subtract psi phi))
      (arithmetic.squareRoot (arithmetic.add psi phi))
  later_division_normalized : 0 < k.val → ∀ i : Fin m,
    arithmetic.normalized (v i / R k k)
  later_normalization_relation : 0 < k.val → ∀ i : Fin m,
    Q i k = arithmetic.divide (v i) (R k k)
  diagonal_pos : 0 < R k k

/-- One successful normalized finite CGS-P execution at machine unit
`epsilonM`. Every leading inverse refers to the computed prefix from this
execution; the family below imposes condition (3) on its common neighborhood. -/
structure P11CGSPTheorem1Run (m n : ℕ) (epsilonM : ℝ) where
  row_dimension_pos : 0 < m
  column_dimension_pos : 0 < n
  columns_le_rows : n ≤ m
  A : P11RectMatrix m n
  Q : P11RectMatrix m n
  R : P11Matrix n
  full_column_rank : Function.Injective A.mulVec
  R_upper_triangular : ∀ i j : Fin n, j.val < i.val → R i j = 0
  arithmetic : P11CGSPNormalizedArithmetic epsilonM
  leadingInverse : ∀ k : Fin n, P11Matrix (k.val + 1)
  leading_left_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (leadingInverse k) (p11LeadingBlock R k) =
      p11Identity (k.val + 1)
  leading_right_inverse : ∀ k : Fin n,
    p11MatMul (k.val + 1) (p11LeadingBlock R k) (leadingInverse k) =
      p11Identity (k.val + 1)
  algorithm2_trace : ∀ k : Fin n,
    P11CGSPColumnTrace arithmetic A Q R k

/-- Positive machine units used to state the source's asymptotic first-order
claim without choosing a remainder independently at one fixed precision. -/
abbrev P11PositiveEpsilon := {epsilonM : ℝ // 0 < epsilonM}

/-- A fixed-input family of operational CGS-P executions as machine precision
tends to zero. The norm bounds record only the local boundedness needed to
propagate a uniform second-order remainder through the computed inverses. -/
structure P11CGSPTheorem1Family (m n : ℕ) where
  A : P11RectMatrix m n
  run : ∀ epsilonM : P11PositiveEpsilon,
    P11CGSPTheorem1Run m n epsilonM.1
  input_fixed : ∀ epsilonM, (run epsilonM).A = A
  rNormBound : Fin n → ℝ
  inverseNormBound : Fin n → ℝ
  normBoundRadius : ℝ
  conditionRadius : ℝ
  r_norm_bound_nonneg : ∀ k, 0 ≤ rNormBound k
  inverse_norm_bound_nonneg : ∀ k, 0 ≤ inverseNormBound k
  norm_bound_radius_pos : 0 < normBoundRadius
  condition_radius_pos : 0 < conditionRadius
  r_norm_bound : ∀ epsilonM, epsilonM.1 ≤ normBoundRadius → ∀ k,
    p11OpNorm2 (p11LeadingBlock (run epsilonM).R k) ≤ rNormBound k
  inverse_norm_bound : ∀ epsilonM, epsilonM.1 ≤ normBoundRadius → ∀ k,
    p11OpNorm2 ((run epsilonM).leadingInverse k) ≤ inverseNormBound k
  condition_3 : ∀ epsilonM, epsilonM.1 ≤ conditionRadius → ∀ k,
    p11C4 m (k.val + 1) * epsilonM.1 *
        p11Kappa2 (p11LeadingBlock (run epsilonM).R k)
          ((run epsilonM).leadingInverse k) ^ 2 < 1

/-- The actual factorization residual for a family member and prefix. -/
noncomputable def p11Theorem1FactorizationResidual {m n : ℕ}
    (family : P11CGSPTheorem1Family m n) (epsilonM : P11PositiveEpsilon)
    (k : Fin n) : P11RectMatrix m (k.val + 1) :=
  p11RectMatMul (p11ColumnPrefix (family.run epsilonM).Q k)
      (p11LeadingBlock (family.run epsilonM).R k) -
    p11ColumnPrefix family.A k

/-- Equations (4), (5), and the reversed form of (6), interpreted uniformly
on one right neighborhood of zero. These are the preceding source results used
in the appendix derivation of equation (7), not fields of an execution. -/
structure P11Theorem1ResidualAsymptotics {m n : ℕ}
    (family : P11CGSPTheorem1Family m n) where
  factorizationSecondOrderCoeff : Fin n → ℝ
  normalEquationSecondOrderCoeff : Fin n → ℝ
  reverseNormSecondOrderCoeff : Fin n → ℝ
  radius : ℝ
  factorization_second_order_nonneg : ∀ k,
    0 ≤ factorizationSecondOrderCoeff k
  normal_equation_second_order_nonneg : ∀ k,
    0 ≤ normalEquationSecondOrderCoeff k
  reverse_norm_second_order_nonneg : ∀ k,
    0 ≤ reverseNormSecondOrderCoeff k
  radius_pos : 0 < radius
  factorization_bound : ∀ epsilonM, epsilonM.1 ≤ radius → ∀ k,
    p11RectOpNorm2 (p11Theorem1FactorizationResidual family epsilonM k) ≤
      p11C1 m (k.val + 1) *
          p11RectOpNorm2 (p11ColumnPrefix family.A k) * epsilonM.1 +
        factorizationSecondOrderCoeff k * epsilonM.1 ^ 2
  normal_equation_bound : ∀ epsilonM, epsilonM.1 ≤ radius → ∀ k,
    p11OpNorm2
        (p11RectNormalEquationResidual
          (p11ColumnPrefix family.A k)
          (p11LeadingBlock (family.run epsilonM).R k)) ≤
      p11C2 m (k.val + 1) *
          p11RectOpNorm2 (p11ColumnPrefix family.A k) ^ 2 * epsilonM.1 +
        normalEquationSecondOrderCoeff k * epsilonM.1 ^ 2
  reverse_norm_bound : ∀ epsilonM, epsilonM.1 ≤ radius → ∀ k,
    p11RectOpNorm2 (p11ColumnPrefix family.A k) ≤
      (1 + p11C3 m (k.val + 1) * epsilonM.1) *
          p11OpNorm2 (p11LeadingBlock (family.run epsilonM).R k) +
        reverseNormSecondOrderCoeff k * epsilonM.1 ^ 2

/-- A common right-neighborhood radius on which the residual estimates,
bounded computed factors, and `epsilonM ≤ 1` are all available. -/
noncomputable def p11Theorem1OrthogonalityRadius {m n : ℕ}
    (family : P11CGSPTheorem1Family m n)
    (analysis : P11Theorem1ResidualAsymptotics family) : ℝ :=
  min 1
    (min family.normBoundRadius (min family.conditionRadius analysis.radius))

/-- A uniform coefficient for the `O(epsilonM^2)` term produced by the
appendix derivation of equation (7). It depends on the fixed family and the
uniform remainders in the preceding equations, never on one chosen epsilon. -/
noncomputable def p11Theorem1OrthogonalityRemainderCoeff {m n : ℕ}
    (family : P11CGSPTheorem1Family m n)
    (analysis : P11Theorem1ResidualAsymptotics family) (k : Fin n) : ℝ :=
  let a := p11RectOpNorm2 (p11ColumnPrefix family.A k)
  let rBound := family.rNormBound k
  let inverseBound := family.inverseNormBound k
  let normSlope :=
    p11C3 m (k.val + 1) * rBound +
      analysis.reverseNormSecondOrderCoeff k
  let aSquareRemainder := 2 * rBound * normSlope + normSlope ^ 2
  let coreRemainder :=
    analysis.normalEquationSecondOrderCoeff k +
      2 * a * analysis.factorizationSecondOrderCoeff k +
      (p11C1 m (k.val + 1) * a +
          analysis.factorizationSecondOrderCoeff k) ^ 2
  inverseBound ^ 2 *
    (p11C4 m (k.val + 1) * aSquareRemainder + coreRemainder)

end HighamBench
