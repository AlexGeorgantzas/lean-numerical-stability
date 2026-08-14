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

/-- Exact induced spectral 2-norm used in P11. -/
noncomputable def p11OpNorm2 {n : ℕ} (A : P11Matrix n) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm A

/-- The paper's first residual coefficient `c1(m,k)`. -/
noncomputable def p11C1 (m k : ℕ) : ℝ :=
  if k = 1 then 1
  else 2 * Real.sqrt (2 * (m : ℝ) * (k : ℝ)) + 2 * Real.sqrt (k : ℝ)

/-- The paper's normal-equations coefficient `c2(m,k)`. -/
noncomputable def p11C2 (m k : ℕ) : ℝ :=
  if k = 1 then (m : ℝ) + 2
  else
    ((7 : ℝ) / 2) * (m : ℝ) * (k : ℝ) ^ 2 -
      ((3 : ℝ) / 2) * (m : ℝ) * (k : ℝ) + 16 * (k : ℝ)

/-- The paper's condition-(3) coefficient `c4 = c2 + 2*c1`. -/
noncomputable def p11C4 (m k : ℕ) : ℝ :=
  p11C2 m k + 2 * p11C1 m k

/-- Exact spectral condition number represented by a matrix and certified inverse. -/
noncomputable def p11Kappa2 {n : ℕ} (R Rinv : P11Matrix n) : ℝ :=
  p11OpNorm2 R * p11OpNorm2 Rinv

/-- Normalized-range floating-point certificate for Algorithm 2's first
column division. It is exactly the standard-error-bound representation used
immediately before equation (16), without assigning unprinted entries to G1. -/
structure P11NormalizedFirstColumn {m : ℕ}
    (a q : Fin m → ℝ) (r11 epsilonM : ℝ) where
  G1 : P11Matrix m
  denominator_pos : 0 < r11
  representation : ∀ i : Fin m,
    q i = (a i + p11MatVec G1 a i) / r11
  opNorm_bound : p11OpNorm2 G1 ≤ epsilonM

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
  epsilonM_nonneg : 0 ≤ epsilonM
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
  first_normalization :
    P11NormalizedFirstColumn
      (fun i => A i (p11FirstIndex column_dimension_pos))
      (fun i => Q i (p11FirstIndex column_dimension_pos))
      (R (p11FirstIndex column_dimension_pos)
        (p11FirstIndex column_dimension_pos))
      epsilonM

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

/-- The complete exact first-column residual identity and norm chain in (16). -/
structure P11Equation16 {m n : ℕ} (run : P11CGSPFirstColumnRun m n) : Prop where
  normalization_relation : ∀ i : Fin m,
    run.Q i (p11FirstIndex run.column_dimension_pos) =
      (run.A i (p11FirstIndex run.column_dimension_pos) +
          p11MatVec run.first_normalization.G1
            (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i) /
        run.R (p11FirstIndex run.column_dimension_pos)
          (p11FirstIndex run.column_dimension_pos)
  perturbation_opNorm_bound :
    p11OpNorm2 run.first_normalization.G1 ≤ run.epsilonM
  factorization_residual_identity :
    p11FirstColumnFactorizationResidual run =
      fun i _ => p11FirstColumnResidualVector run i
  residual_action_identity :
    p11FirstColumnResidualVector run =
      fun i =>
        -p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) i
  matrix_vector_norm_identity :
    p11FirstColumnMatrixNorm2 (p11FirstColumnFactorizationResidual run) =
      p11VecNorm (p11FirstColumnResidualVector run)
  residual_action_norm_identity :
    p11VecNorm (p11FirstColumnResidualVector run) =
      p11VecNorm
        (p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos)))
  operator_action_bound :
    p11VecNorm
        (p11MatVec run.first_normalization.G1
          (fun j => run.A j (p11FirstIndex run.column_dimension_pos))) ≤
      p11OpNorm2 run.first_normalization.G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))
  machine_unit_bound :
    p11OpNorm2 run.first_normalization.G1 *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos)) ≤
      run.epsilonM *
        p11VecNorm (fun j => run.A j (p11FirstIndex run.column_dimension_pos))

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

end HighamBench
