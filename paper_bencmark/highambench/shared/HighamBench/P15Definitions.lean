import HighamBench.Core
import Mathlib.Analysis.Matrix.Normed

/-!
# HighamBench P15 definitions

Paper-scoped finite matrix notation for Higham and Mary's analysis of
low-rank matrix computations.
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

/-- The low-rank matrix representation `Atilde = X Y^T`. -/
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

/-- The real gamma index `c = b + 2*r^(3/2)` in equations (3.10)--(3.11). -/
noncomputable def p15LowRankMatMulCost (b r : ℕ) : ℝ :=
  (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ)

/-- One rounded matrix-multiplication stage using the recalled equation-(2.7)
Frobenius forward-error interface. The inner dimension is `n`; the computed
output is defined as the exact product plus this local error. -/
structure P15RoundedMatMulStage (m n p : ℕ) (u : ℝ)
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) where
  error : P15RectMatrix m p
  error_le : p15RectFrobNorm error ≤
    p15GammaReal (n : ℝ) u * p15RectFrobNorm A * p15RectFrobNorm B

/-- The output represented by one rounded matrix-multiplication stage. -/
noncomputable def P15RoundedMatMulStage.result {m n p : ℕ} {u : ℝ}
    {A : P15RectMatrix m n} {B : P15RectMatrix n p}
    (stage : P15RoundedMatMulStage m n p u A B) : P15RectMatrix m p :=
  p15RectMatMul A B + stage.error

/-- The raw three-product execution for either parenthesization in Lemma 3.3.
Only stage equations and equation-(2.7) bounds are stored; neither final error
bound is an input. -/
inductive P15LowRankMatMulTrace {b r : ℕ} (u : ℝ)
    (XA YA XB YB : P15RectMatrix b r) where
  | leftAssociated
      (middleStage : P15RoundedMatMulStage r b r u
        (p15RectTranspose YA) YB)
      (leftStage : P15RoundedMatMulStage b r r u XA middleStage.result)
      (finalStage : P15RoundedMatMulStage b r b u leftStage.result
        (p15RectTranspose XB))
  | rightAssociated
      (middleStage : P15RoundedMatMulStage r b r u
        (p15RectTranspose YA) YB)
      (rightStage : P15RoundedMatMulStage r r b u middleStage.result
        (p15RectTranspose XB))
      (finalStage : P15RoundedMatMulStage b r b u XA rightStage.result)

/-- The computed matrix produced by a Lemma-3.3 three-product trace. -/
noncomputable def P15LowRankMatMulTrace.result {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P15RectMatrix b r}
    (trace : P15LowRankMatMulTrace u XA YA XB YB) : P15Matrix b :=
  match trace with
  | .leftAssociated _ _ finalStage => finalStage.result
  | .rightAssociated _ _ finalStage => finalStage.result

/-- One source-level execution of Lemma 3.3. The low-rank approximation errors
and all three rounded products remain separate from the two aggregate bounds
proved by the benchmark target. -/
structure P15LowRankMatMulExecution (b r : ℕ) where
  A : P15Matrix b
  B : P15Matrix b
  XA : P15RectMatrix b r
  YA : P15RectMatrix b r
  XB : P15RectMatrix b r
  YB : P15RectMatrix b r
  epsilon : ℝ
  betaA : ℝ
  betaB : ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  gamma_valid :
    p15LowRankMatMulCost b r * unitRoundoff < 1
  xA_orthonormal : p15OrthonormalColumns XA
  xB_orthonormal : p15OrthonormalColumns XB
  approximationErrorA : P15Matrix b
  approximationErrorB : P15Matrix b
  approximationA_eq :
    p15LowRankMatrix XA YA = A + approximationErrorA
  approximationB_eq :
    p15LowRankMatrix YB XB = B + approximationErrorB
  approximationErrorA_le :
    p15FrobNorm approximationErrorA ≤ epsilon * betaA
  approximationErrorB_le :
    p15FrobNorm approximationErrorB ≤ epsilon * betaB
  trace : P15LowRankMatMulTrace unitRoundoff XA YA XB YB

end HighamBench
