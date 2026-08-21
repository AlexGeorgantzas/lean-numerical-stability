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
    2 * Real.sqrt (2 * (m : ℝ)) * (k : ℝ) +
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

/-- Exact inner product underlying one entry of `s_k = Q_(k-1)^T a_k`. -/
noncomputable def p11CGSPProjectionEntry {m n : ℕ}
    (A Q : P11RectMatrix m n) (j k : Fin n) : ℝ :=
  ∑ i : Fin m, Q i j * A i k

/-- Exact residual underlying `v_k = a_k - Q_(k-1) s_k`. -/
noncomputable def p11CGSPResidualEntry {m n : ℕ}
    (A Q : P11RectMatrix m n) (s : Fin n → ℝ)
    (i : Fin m) (k : Fin n) : ℝ :=
  A i k - ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < k.val),
    Q i j * s j

/-- One column of a successful normalized-range CGS-P execution. The named
local errors expose a permissive first-order envelope for the pseudo-code
operations whose primitive evaluation order the paper leaves unspecified. -/
structure P11CGSPColumnTrace {m n : ℕ}
    (A Q : P11RectMatrix m n) (R : P11Matrix n)
    (epsilonM : ℝ) (k : Fin n) where
  s : Fin n → ℝ
  v : Fin m → ℝ
  psi : ℝ
  phi : ℝ
  projectionError : Fin n → ℝ
  residualError : Fin m → ℝ
  psiError : ℝ
  phiError : ℝ
  diagonalError : ℝ
  normalizationError : Fin m → ℝ
  localErrorScale : ℝ
  local_error_scale_nonneg : 0 ≤ localErrorScale
  projection_support : ∀ j : Fin n, k.val ≤ j.val → s j = 0
  first_diagonal_relation : k.val = 0 →
    R k k = p11CGSPColumnNorm A k + diagonalError
  first_normalization_relation : k.val = 0 → ∀ i : Fin m,
    Q i k = A i k / R k k + normalizationError i
  later_projection_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val →
      s j = p11CGSPProjectionEntry A Q j k + projectionError j
  later_upper_factor_relation : 0 < k.val → ∀ j : Fin n,
    j.val < k.val → R j k = s j
  later_residual_relation : 0 < k.val → ∀ i : Fin m,
    v i = p11CGSPResidualEntry A Q s i k + residualError i
  later_psi_relation : 0 < k.val →
    psi = p11CGSPColumnNorm A k + psiError
  later_phi_relation : 0 < k.val →
    phi = p11VecNorm s + phiError
  later_psi_nonneg : 0 < k.val → 0 ≤ psi
  later_phi_nonneg : 0 < k.val → 0 ≤ phi
  later_pythagorean_domain : 0 < k.val → 0 ≤ psi - phi
  later_diagonal_relation : 0 < k.val →
    R k k = Real.sqrt (psi - phi) * Real.sqrt (psi + phi) + diagonalError
  later_normalization_relation : 0 < k.val → ∀ i : Fin m,
    Q i k = v i / R k k + normalizationError i
  diagonal_pos : 0 < R k k
  projection_error_bound : ∀ j,
    |projectionError j| ≤ localErrorScale * epsilonM
  residual_error_bound : ∀ i,
    |residualError i| ≤ localErrorScale * epsilonM
  psi_error_bound : |psiError| ≤ localErrorScale * epsilonM
  phi_error_bound : |phiError| ≤ localErrorScale * epsilonM
  diagonal_error_bound : |diagonalError| ≤ localErrorScale * epsilonM
  normalization_error_bound : ∀ i,
    |normalizationError i| ≤ localErrorScale * epsilonM

/-- The source-level data used for one prefix in the proof of Theorem 1(7).
The three coefficients expose the otherwise unspecified finite constants in
the `O(epsilonM^2)` terms of (4), (5), and the reversed form of (6). -/
structure P11Theorem1PrefixCertificate {m k : ℕ}
    (A Q : P11RectMatrix m k) (R : P11Matrix k) (epsilonM : ℝ) where
  deltaA : P11RectMatrix m k
  normalEquationResidual : P11Matrix k
  factorizationSecondOrderCoeff : ℝ
  normalEquationSecondOrderCoeff : ℝ
  reverseNormSecondOrderCoeff : ℝ
  factorization_second_order_nonneg : 0 ≤ factorizationSecondOrderCoeff
  normal_equation_second_order_nonneg :
    0 ≤ normalEquationSecondOrderCoeff
  reverse_norm_second_order_nonneg : 0 ≤ reverseNormSecondOrderCoeff
  factorization_relation : p11RectMatMul Q R = A + deltaA
  normal_equation_relation :
    normalEquationResidual = p11RectNormalEquationResidual A R
  factorization_bound :
    p11RectOpNorm2 deltaA ≤
      p11C1 m k * p11RectOpNorm2 A * epsilonM +
        factorizationSecondOrderCoeff * epsilonM ^ 2
  normal_equation_bound :
    p11OpNorm2 normalEquationResidual ≤
      p11C2 m k * p11RectOpNorm2 A ^ 2 * epsilonM +
        normalEquationSecondOrderCoeff * epsilonM ^ 2
  reverse_norm_bound :
    p11RectOpNorm2 A ≤
      (1 + p11C3 m k * epsilonM) * p11OpNorm2 R +
        reverseNormSecondOrderCoeff * epsilonM ^ 2

/-- A proof-carrying successful normalized-range CGS-P execution in the
analytic model of Theorem 1. It keeps one rectangular input and one computed
`Q,R` pair, then links every positive leading prefix to equations (3)--(6).
The paper does not specify a complete primitive-operation semantics, so this
contract records exactly the real-valued execution facts used to derive (7). -/
structure P11CGSPTheorem1Run (m n : ℕ) where
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
  algorithm2_trace : ∀ k : Fin n,
    P11CGSPColumnTrace A Q R epsilonM k
  prefixCertificate : ∀ k : Fin n,
    P11Theorem1PrefixCertificate
      (p11ColumnPrefix A k) (p11ColumnPrefix Q k)
      (p11LeadingBlock R k) epsilonM

/-- The explicit finite coefficient multiplying `epsilonM^2` in the repaired
form of Theorem 1(7). It is derived from the three source-level remainder
coefficients fixed by the prefix certificate. -/
noncomputable def p11Theorem1OrthogonalityRemainderCoeff {m n : ℕ}
    (run : P11CGSPTheorem1Run m n) (k : Fin n) : ℝ :=
  let certificate := run.prefixCertificate k
  let a := p11RectOpNorm2 (p11ColumnPrefix run.A k)
  let r := p11OpNorm2 (p11LeadingBlock run.R k)
  let rinv := p11OpNorm2 (run.leadingInverse k)
  let normSlope :=
    p11C3 m (k.val + 1) * r + certificate.reverseNormSecondOrderCoeff
  let aSquareRemainder := 2 * r * normSlope + normSlope ^ 2
  let coreRemainder :=
    certificate.normalEquationSecondOrderCoeff +
      2 * a * certificate.factorizationSecondOrderCoeff +
      (p11C1 m (k.val + 1) * a +
          certificate.factorizationSecondOrderCoeff) ^ 2
  rinv ^ 2 *
    (p11C4 m (k.val + 1) * aSquareRemainder + coreRemainder)

end HighamBench
