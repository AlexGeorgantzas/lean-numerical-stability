-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): backward stable; currently represented by
-- an abstract Gram-system predicate while the rectangular QR bridge is open.
-- The full source theorem requires rectangular QR.
--
-- SNE method: solves RᵀRy = b via Cholesky-like approach. The
-- backward error is proved by composing with existing Cholesky
-- solve results. The forward error (eq. 21.11) follows from
-- normwise_perturbation_bound (Theorem 7.2).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanFpAnalysis.FP.Model
import LeanFpAnalysis.FP.Analysis.Rounding
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Analysis.PerturbationTheory
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySpec
import LeanFpAnalysis.FP.Algorithms.Cholesky.CholeskySolve
import LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve
import LeanFpAnalysis.FP.Algorithms.Underdetermined.UnderdeterminedSpec

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  QR block algebra for the Q method and SNE setup
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.1):
    source-facing wrapper for multiplying by the tall QR block `[R; 0]`
    appearing in `Aᵀ = Q [R; 0]`. -/
theorem higham21_eq21_1_qr_transpose_block_mulVec {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (x : Fin m → ℝ) :
    rectMatMulVec (lsQRTallBlock (k := k) R) x =
      Fin.append (rectMatMulVec R x) (0 : Fin k → ℝ) :=
  lsQRTallBlock_mulVec R x

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.2):
    source-facing wrapper for the block-transpose coordinate identity
    `[Rᵀ 0] [y₁; y₂] = Rᵀ y₁`.  This is the algebraic step behind reducing
    `b = A x` to the triangular equation for the first coordinate block after
    applying the orthogonal factor from (21.1). -/
theorem higham21_eq21_2_qr_block_transpose_coordinates {m k : ℕ}
    (R : Fin m → Fin m → ℝ) (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    (fun j : Fin m =>
      ∑ i : Fin (m + k), lsQRTallBlock (k := k) R i j *
        Fin.append y1 y2 i) =
      fun j : Fin m => ∑ i : Fin m, R i j * y1 i :=
  lsQRTallBlock_transpose_mulVec_append R y1 y2

/-- Higham, 2nd ed., Chapter 21, Section 21.1, equation (21.3):
    source-facing algebraic wrapper for the minimum-norm coordinate choice
    in the Q method.  Among coordinate vectors with the same first block,
    setting the free second block to zero gives no larger Euclidean norm.
    This is the norm-minimization step only; the full orthogonal `Q` handoff
    and triangular solve formula remain separate selected targets. -/
theorem higham21_eq21_3_free_coordinate_zero_min_norm {m k : ℕ}
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) ≤
      vecNorm2 (Fin.append y1 y2) := by
  have hzero :
      vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := by
    unfold vecNorm2
    rw [lsVecNorm2Sq_append]
    simp [vecNorm2Sq]
  calc
    vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) = vecNorm2 y1 := hzero
    _ ≤ vecNorm2 (Fin.append y1 y2) := lsVecNorm2_left_le_append y1 y2

-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    a row-wise backward-error witness for an underdetermined system.

    The computed vector `x_hat` is the exact minimum 2-norm solution of the
    row-wise perturbed rectangular system `(A + ΔA) x = b`, and each row
    perturbation is bounded relative to the corresponding row of `A` in the
    Euclidean norm. -/
structure UndetRowwiseBackwardErrorFeasible (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop where
  /-- The row-wise error factor is nonnegative. -/
  eta_nonneg : 0 ≤ eta
  /-- `x_hat` is the minimum 2-norm solution of the perturbed system. -/
  min_norm :
    RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat
  /-- Each row perturbation is bounded by `eta` times the original row norm. -/
  row_bound : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i

/-- Existence form of the Chapter 21 row-wise backward-error predicate. -/
def UndetRowwiseBackwardErrorBounded (m n : ℕ)
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ) : Prop :=
  ∃ ΔA : Fin m → Fin n → ℝ,
    UndetRowwiseBackwardErrorFeasible m n A ΔA b x_hat eta

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing constructor for a row-wise backward-error certificate.
    This packages the definition used by Theorem 21.4; it does not by itself
    prove that a particular QR implementation supplies such a witness. -/
theorem higham21_rowwise_backward_error_bound_witness
    (m n : ℕ)
    (A ΔA : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (x_hat : Fin n → ℝ)
    (eta : ℝ)
    (heta : 0 ≤ eta)
    (hmin :
      RectMinNormSolution m n (fun i j => A i j + ΔA i j) b x_hat)
    (hrow : ∀ i : Fin m, rectRowNorm2 ΔA i ≤ eta * rectRowNorm2 A i) :
    UndetRowwiseBackwardErrorBounded m n A b x_hat eta :=
  ⟨ΔA, ⟨heta, hmin, hrow⟩⟩

-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    feasibility predicate for the normwise Frobenius backward error
    `eta_F(y)` of an approximate minimum 2-norm underdetermined solution.

    This reuses the Chapter 20 weighted Frobenius perturbation cost
    `||[DeltaA, theta Delta b]||_F`; the Ch21-specific change is that `y`
    must be a minimum 2-norm solution of the perturbed rectangular system. -/
def UndetNormwiseBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  RectMinNormSolution m n
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y

/-- Attainable weighted Frobenius costs in the Chapter 21 Theorem 21.3
    normwise backward-error definition. -/
noncomputable def undetNormwiseBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}

/-- Infimum model of Higham Chapter 21 Theorem 21.3's normwise backward
    error `eta_F(y)`.  The source writes a minimum and gives the Sun-Sun
    closed formula; those attainment and singular-value formula rows remain
    separate selected targets. -/
noncomputable def undetNormwiseBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (undetNormwiseBackwardErrorValuesF theta A b y)

/-- The Chapter 21 attainable-cost set is bounded below by zero. -/
theorem undetNormwiseBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (undetNormwiseBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- The Chapter 21 normwise backward-error infimum model is nonnegative. -/
theorem undetNormwiseBackwardErrorEtaF_nonneg {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    0 ≤ undetNormwiseBackwardErrorEtaF theta A b y := by
  unfold undetNormwiseBackwardErrorEtaF
  apply Real.sInf_nonneg
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab

/-- Zero is an attainable Chapter 21 normwise backward-error cost when `y`
    is already a minimum 2-norm solution of the original data. -/
theorem undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    (0 : ℝ) ∈ undetNormwiseBackwardErrorValuesF theta A b y := by
  rw [← lsNormwiseBackwardErrorCostF_zero (m := m) (n := n) theta]
  refine ⟨(0 : Fin m → Fin n → ℝ), (0 : Fin m → ℝ), ?_, rfl⟩
  simpa [UndetNormwiseBackwardErrorFeasible] using hmin

/-- If `y` is already a minimum 2-norm solution of the original data, then
    the Chapter 21 infimum model gives zero backward error. -/
theorem undetNormwiseBackwardErrorEtaF_eq_zero_of_rectMinNormSolution
    {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (hmin : RectMinNormSolution m n A b y) :
    undetNormwiseBackwardErrorEtaF theta A b y = 0 := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le (undetNormwiseBackwardErrorValuesF.bddBelow theta A b y)
      (undetNormwiseBackwardErrorValuesF.zero_mem_of_rectMinNormSolution
        theta A b y hmin)
  · exact undetNormwiseBackwardErrorEtaF_nonneg theta A b y

/-- In the Chapter 21 Theorem 21.3 weighted Frobenius model, perturbing only
    the right-hand side by `-b` has cost `theta * ||b||_2`, for nonnegative
    source weight `theta`. -/
theorem undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta) (b : Fin m → ℝ) :
    lsNormwiseBackwardErrorCostF (m := m) (n := n) theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) = theta * vecNorm2 b := by
  have hleft : 0 ≤ lsNormwiseBackwardErrorCostF theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i) :=
    lsNormwiseBackwardErrorCostF_nonneg theta
      (0 : Fin m → Fin n → ℝ) (fun i => -b i)
  have hright : 0 ≤ theta * vecNorm2 b :=
    mul_nonneg htheta (vecNorm2_nonneg b)
  apply (sq_eq_sq₀ hleft hright).mp
  rw [lsNormwiseBackwardErrorCostF_sq]
  rw [show frobNormSqRect (0 : Fin m → Fin n → ℝ) = 0 by
    simp [frobNormSqRect]]
  have hneg : vecNorm2Sq (fun i : Fin m => -b i) = vecNorm2Sq b := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg]
  rw [show (theta * vecNorm2 b) ^ 2 = theta ^ 2 * vecNorm2 b ^ 2 by ring]
  rw [vecNorm2_sq]
  ring

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source zero-vector candidate `y = 0` has attainable cost
    `theta * ||b||_2` in the underdetermined normwise backward-error model. -/
theorem undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    theta * vecNorm2 b ∈
      undetNormwiseBackwardErrorValuesF theta A b (0 : Fin n → ℝ) := by
  refine ⟨(0 : Fin m → Fin n → ℝ), (fun i => -b i), ?_, ?_⟩
  · unfold UndetNormwiseBackwardErrorFeasible
    constructor
    · ext i
      simp [rectMatMulVec]
    · intro z _hz
      change vecNorm2 (fun _ : Fin n => 0) ≤ vecNorm2 z
      rw [vecNorm2_zero]
      exact vecNorm2_nonneg z
  · exact (undetNormwiseBackwardErrorCostF_zero_deltaA_neg_deltab
      theta htheta b).symm

/-- Any feasible perturbation for the Chapter 21 zero-vector candidate must
    pay at least the weighted right-hand-side cost `theta * ||b||_2`. -/
theorem undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
    {m n : ℕ} {theta : ℝ} (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (hfeas :
      UndetNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ) DeltaA Deltab) :
    theta * vecNorm2 b ≤ lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  have hDeltab : Deltab = fun i : Fin m => -b i := by
    ext i
    have hi := congrFun hfeas.system_eq i
    have hzero : (0 : ℝ) = b i + Deltab i := by
      simpa [rectMatMulVec] using hi
    linarith
  have hweighted : theta * vecNorm2 Deltab ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab :=
    lsNormwiseBackwardErrorCostF_weighted_deltab_le htheta DeltaA Deltab
  simpa [hDeltab, vecNorm2_neg] using hweighted

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    zero-vector branch of the Sun--Sun normwise Frobenius backward-error
    formula, `eta_F(0) = theta * ||b||_2`, stated for nonnegative `theta`.
    The nonzero singular-value formula remains a separate selected target. -/
theorem higham21_thm21_3_etaF_zero
    {m n : ℕ} (theta : ℝ) (htheta : 0 ≤ theta)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    undetNormwiseBackwardErrorEtaF theta A b (0 : Fin n → ℝ) =
      theta * vecNorm2 b := by
  apply le_antisymm
  · unfold undetNormwiseBackwardErrorEtaF
    exact csInf_le
      (undetNormwiseBackwardErrorValuesF.bddBelow theta A b (0 : Fin n → ℝ))
      (undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b)
  · unfold undetNormwiseBackwardErrorEtaF
    apply le_csInf
    · exact ⟨theta * vecNorm2 b,
        undetNormwiseBackwardErrorValuesF.theta_vecNorm_mem_zero theta htheta A b⟩
    · intro eta heta
      rcases heta with ⟨DeltaA, Deltab, hfeas, rfl⟩
      exact undetNormwiseBackwardErrorCostF_ge_theta_vecNorm_of_zero_feasible
        htheta A b DeltaA Deltab hfeas

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    residual for an approximate underdetermined solution, using the source
    sign convention `r = b - A y`. -/
noncomputable def undetResidualHigham {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    Fin m → ℝ :=
  fun i => b i - rectMatMulVec A y i

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source-facing model of `I - y y^+` in the nonzero-`y` branch.  This reuses
    the Chapter 20 rank-one complement-projector infrastructure. -/
noncomputable abbrev undetApproxComplementProjector {n : ℕ}
    (y : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  lsResidualComplementProjector y

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    source matrix `A(I - y y^+)` appearing in the nonzero Sun--Sun formula. -/
noncomputable def undetNormwiseBackwardErrorFormulaMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  rectMatMul A (undetApproxComplementProjector y)

/-- Entry expansion of the Chapter 21 source matrix `A(I - y y^+)`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_apply {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    undetNormwiseBackwardErrorFormulaMatrix A y i j =
      ∑ k : Fin n, A i k *
        (idMatrix n k j - y k * y j / vecNorm2Sq y) := by
  rfl

/-- Applying the Chapter 21 source matrix `A(I - y y^+)` is the same as first
    projecting with `I - y y^+`, then applying `A`. -/
theorem undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y x : Fin n → ℝ) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) x =
      rectMatMulVec A (rectMatMulVec (undetApproxComplementProjector y) x) := by
  rw [undetNormwiseBackwardErrorFormulaMatrix, rectMatMulVec_rectMatMul]

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    the source matrix `A(I - y y^+)` annihilates the nonzero candidate
    direction `y`. -/
theorem higham21_thm21_3_formulaMatrix_mulVec_candidate_eq_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ)
    (hysq : vecNorm2Sq y ≠ 0) :
    rectMatMulVec (undetNormwiseBackwardErrorFormulaMatrix A y) y = 0 := by
  have hcomp : rectMatMulVec (undetApproxComplementProjector y) y = 0 := by
    simpa [undetApproxComplementProjector, rectMatMulVec, matMulVec] using
      (lsResidualComplementProjector_mulVec_residual y hysq)
  rw [undetNormwiseBackwardErrorFormulaMatrix_mulVec_eq A y y, hcomp]
  ext i
  simp [rectMatMulVec]

/-- Higham, 2nd ed., Chapter 21, Section 21.2, Theorem 21.3:
    scalar right-hand side of the nonzero Sun--Sun formula, parameterized by
    the smallest singular value of `A(I - y y^+)`.  Proving that this equals
    `eta_F(y)` remains the open singular-value branch. -/
noncomputable def undetNormwiseBackwardErrorNonzeroFormulaRHS {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (sigma : ℝ) : ℝ :=
  Real.sqrt
    (theta ^ 2 * vecNorm2Sq y / (1 + theta ^ 2 * vecNorm2Sq y) *
        (vecNorm2Sq (undetResidualHigham A b y) / vecNorm2Sq y) +
      sigma ^ 2)

-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================

/-- **Theorem 21.4** (Higham): The Q method for underdetermined systems
    is row-wise backward stable.

    The Q method solves Rᵀy₁ = b and forms x = Q[y₁; 0]ᵀ using
    the QR factorization Aᵀ = Q[R; 0]. The computed x̂ is the
    minimum 2-norm solution to (A + ΔA)x = b, where:

    ‖ΔA‖_F ≤ mγ_{cn}‖A‖_F  (normwise)
    |ΔA| ≤ mnγ_{cn}|A|G, ‖G‖_F = 1  (componentwise)

    Note: b is not perturbed (unlike the least-squares QR result in
    Theorem 20.3).

    Recorded as an abstract predicate until the rectangular QR factorization
    bridge and Lemma 21.2 symmetrization route are fully formalized. -/
structure QMethodBackwardStable (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b y_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- c_bound is nonneg. -/
  bound_nonneg : 0 ≤ c_bound
  /-- The computed ŷ satisfies perturbed normal equations
      (AAᵀ + ΔG)ŷ = b with bounded ΔG.
      This captures the Q method's backward stability projected
      to the m×m Gram system AAᵀ. -/
  result : ∃ (ΔG : Fin m → Fin m → ℝ),
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) y_hat i = b i) ∧
    frobNorm ΔG ≤ c_bound

-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================

/-- **SNE method backward error for underdetermined systems** (Higham §21.3).

    The SNE method solves RᵀRy = b where Aᵀ = Q[R; 0], then forms
    x = Aᵀy. The solve RᵀRy = b is equivalent to Cholesky-solving
    the m×m system AAᵀy = b (since AAᵀ = RᵀR for the exact R).

    The backward error of the Cholesky solve gives:
    (RᵀR + ΔC)ŷ = b where |ΔC| ≤ (γ(m+1) + 2γ(m) + γ(m)²)·|R̂ᵀ||R̂|

    This is a direct application of `cholesky_solve_backward_error_expanded`
    from CholeskySolve.lean with n := m (the Gram matrix is m×m). -/
theorem sne_backward_error (fp : FPModel) (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
    let R_hatT := fun i j : Fin m => R_hat j i
    let y_hat := fl_forwardSub fp m R_hatT b
    let x_hat := fl_backSub fp m R_hat y_hat
    ∃ ΔC : Fin m → Fin m → ℝ,
      (∀ i j, |ΔC i j| ≤
        (gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2) *
          ∑ k : Fin m, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * x_hat j = b i) :=
  cholesky_solve_backward_error_expanded fp m AAT R_hat b hR_diag hChol hm1

-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================

/-- **Forward error for underdetermined system solve** (Higham §21.3, eq. 21.11).

    For both the Q method and SNE method, the forward error satisfies:
    ‖x̂ − x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    where cond₂(A) = ‖|A⁺||A|‖₂. Note this bound is independent
    of the row scaling of A.

    We prove the componentwise form: given backward error in the
    m×m Gram system, the forward error is bounded by
    |ŷ − y| ≤ |(AAᵀ)⁻¹| · |ΔG · ŷ|.

    This reuses `normwise_perturbation_bound` (Theorem 7.2) from
    PerturbationTheory.lean, noting that Δb = 0 for the Q method
    (the right-hand side b is not perturbed). -/
theorem underdetermined_forward_error (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| := by
  -- Since Δb = 0, the bound from Theorem 7.2 simplifies to
  -- |ŷ − y| ≤ |(AAᵀ)⁻¹| · (|ΔG|·|ŷ| + 0)
  -- We apply normwise_perturbation_bound with Δb := 0.
  let Δb : Fin m → ℝ := fun _ => 0
  have hPerturbed' : ∀ i, ∑ j, (AAT i j + ΔG i j) * y_hat j = b i + Δb i := by
    intro i; simp [Δb]; exact hPerturbed i
  have hExact' : ∀ i, ∑ j, AAT i j * y j = b i := fun i => hExact i
  have hBound := normwise_perturbation_bound m AAT AAT_inv y y_hat b ΔG Δb
    hInv.1 hExact' hPerturbed'
  intro i
  rw [abs_sub_comm]
  have h := hBound i
  -- Simplify: |Δb_j| = 0, so ∑|ΔG|·|ŷ| + |Δb| = ∑|ΔG|·|ŷ| + 0
  calc |y i - y_hat i|
      ≤ ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + |Δb j|) := h
    _ = ∑ j, |AAT_inv i j| * (∑ k, |ΔG j k| * |y_hat k| + 0) := by
        simp [Δb]
    _ = ∑ j, |AAT_inv i j| * ∑ k, |ΔG j k| * |y_hat k| := by
        apply Finset.sum_congr rfl; intro j _; ring_nf

/-- **SNE method is NOT backward stable** (Higham §21.3, remark).

    Unlike the Q method (Theorem 21.4), the SNE method does not
    guarantee that x̂ is the minimum 2-norm solution to a nearby
    system. The SNE only guarantees a small residual in the normal
    equations RᵀRŷ ≈ b.

    However, both methods achieve the same forward error bound (eq. 21.11):
    ‖x̂−x‖₂/‖x‖₂ ≤ mnγ'_{cn} · cond₂(A) + O(u²)

    This means the forward error from SNE is as good as from Q method,
    even though the backward error characterization is weaker. -/
theorem sne_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| := by
  -- Same proof as underdetermined_forward_error: apply Theorem 7.2 with Δb = 0
  have hPert' : ∀ i, matMulVec m (fun a c => AAT a c + ΔC a c) y_hat i = b i :=
    fun i => hPerturbed i
  exact underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔC hPert'

/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11):
    source-facing wrapper for the currently formalized Gram-system forward
    perturbation consequence.  This is not the full printed asymptotic
    `mn * gamma * cond_2(A) + O(u^2)` bound; it is the exact componentwise
    perturbation inequality used as a dependency for that row. -/
theorem higham21_eq21_11_gram_forward_error
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔG : Fin m → Fin m → ℝ)
    (hPerturbed :
      ∀ i, matMulVec m (fun a c => AAT a c + ΔG a c) y_hat i = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔG j k| * |y_hat k| :=
  underdetermined_forward_error m AAT AAT_inv hInv b y y_hat hExact ΔG hPerturbed

/-- Higham, 2nd ed., Chapter 21, Section 21.3:
    source-facing wrapper for the proved statement that the SNE Gram-system
    perturbation route has the same componentwise forward-error consequence as
    the Q-method Gram-system route.  The full source statement still requires
    instantiating the QR/SNE computed-object bounds. -/
theorem higham21_sne_gram_forward_error_matches_q_method
    (m : ℕ)
    (AAT AAT_inv : Fin m → Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (b y y_hat : Fin m → ℝ)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (ΔC : Fin m → Fin m → ℝ)
    (hPerturbed : ∀ i, ∑ j : Fin m, (AAT i j + ΔC i j) * y_hat j = b i) :
    ∀ i : Fin m, |y_hat i - y i| ≤
      ∑ j : Fin m, |AAT_inv i j| *
        ∑ k : Fin m, |ΔC j k| * |y_hat k| :=
  sne_forward_error_matches_q_method m AAT AAT_inv hInv b y y_hat hExact ΔC
    hPerturbed

end LeanFpAnalysis.FP
