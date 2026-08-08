import Mathlib.Analysis.InnerProductSpace.PiL2
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.RandomizedLinearAlgebra.LeastSquaresSketching.RowSampling.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Gram
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.NormalEquations
import NumStability.FloatingPoint.Model

/-!
# NumStability.Algorithms.RandomizedLinearAlgebra.LeastSquaresSketching.Objectives.Core

W11 canonical reusable randomized linear algebra destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.LeastSquaresSketch`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/LeastSquaresSketch.lean
--
-- Deterministic least-squares consequences of a sketching/subspace-embedding
-- hypothesis, motivated by CACM RandNLA equation (8).
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602














namespace NumStability

open scoped BigOperators

/-!
## Least-squares sketch objective

Equation (8) in the CACM RandNLA survey is the least-squares problem

`x_opt = argmin_x ||A x - b||₂`.

This file formalizes the deterministic implication used by RandNLA
least-squares algorithms: if a sketch preserves the squared residual objective
for every `x`, then an exact minimizer of the sketched problem is a relative
residual-objective approximation for the original problem.

It does not prove that a particular random sampling or random projection
constructs such a sketch with high probability.  That remains a separate
subspace-embedding/concentration obligation.
-/

/-- A vector is an additive-gap approximate minimizer of the least-squares
    objective.  The gap is intentionally explicit so later solver/preconditioner
    analyses can supply it without being hidden inside the sketch theorem. -/
def IsLeastSquaresApproxMinimizer {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (gap : ℝ) : Prop :=
  ∀ y : Fin n → ℝ, lsObjective A b x ≤ lsObjective A b y + gap

/-- Exact minimizers are approximate minimizers with zero additive gap. -/
theorem isLeastSquaresApproxMinimizer_of_minimizer
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {x : Fin n → ℝ} (h : IsLeastSquaresMinimizer A b x) :
    IsLeastSquaresApproxMinimizer A b x 0 := by
  intro y
  simpa using h y

/-- A sketched least-squares instance preserves every squared residual objective
    within multiplicative factors `1 ± ε`. -/
def PreservesLSObjective {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ) (ε : ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    (1 - ε) * lsObjective A b x ≤ lsObjective SA Sb x ∧
      lsObjective SA Sb x ≤ (1 + ε) * lsObjective A b x



















/-- Floating-point row-sampled least-squares matrix with leverage probabilities
    supplied by a basis matrix `U`.  This is the literal rounded counterpart of
    `rowSampleLSMatrixWithBasisScale`: each sampled entry of `A` is divided by
    the exact scaling denominator using the repository's `fl_div` model. -/
noncomputable def fl_rowSampleLSMatrixWithBasisScale
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => fp.fl_div (A (samples t) j) (rowSampleScaleDen s U (samples t))

/-- Floating-point row-sampled least-squares right-hand side with the same
    basis-probability scaling as `fl_rowSampleLSMatrixWithBasisScale`. -/
noncomputable def fl_rowSampleLSVectorWithBasisScale
    (fp : FPModel) {m d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → ℝ :=
  fun t => fp.fl_div (b (samples t)) (rowSampleScaleDen s U (samples t))

/-- Entrywise forward error for the literal rounded least-squares sketch
    matrix. -/
theorem fl_rowSampleLSMatrixWithBasisScale_error_bound
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |fl_rowSampleLSMatrixWithBasisScale fp s U A samples t j -
      rowSampleLSMatrixWithBasisScale s U A samples t j| ≤
      |rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u := by
  unfold fl_rowSampleLSMatrixWithBasisScale rowSampleLSMatrixWithBasisScale
  exact fl_div_error_bound fp (A (samples t) j)
    (rowSampleScaleDen s U (samples t)) hdenom

/-- Entrywise forward error for the literal rounded least-squares sketch right
    hand side. -/
theorem fl_rowSampleLSVectorWithBasisScale_error_bound
    (fp : FPModel) {m d steps : ℕ} (s : ℕ)
    (U : Fin m → Fin d → ℝ) (b : Fin m → ℝ)
    (samples : RowTrace m steps) (t : Fin steps)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |fl_rowSampleLSVectorWithBasisScale fp s U b samples t -
      rowSampleLSVectorWithBasisScale s U b samples t| ≤
      |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  unfold fl_rowSampleLSVectorWithBasisScale rowSampleLSVectorWithBasisScale
  exact fl_div_error_bound fp (b (samples t))
    (rowSampleScaleDen s U (samples t)) hdenom

/-- Residual perturbation induced by the literal rounded least-squares row
    divisions for one sampled row.  This is the first implementation-backed
    foundation needed before the rounded sketched objective can replace the
    current explicit rounded-Gram representation hypothesis. -/
theorem fl_rowSampleLSResidualWithBasisScale_error_bound
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) (t : Fin steps)
    (hdenom : rowSampleScaleDen s U (samples t) ≠ 0) :
    |lsResidual
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x t -
      lsResidual
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x t| ≤
      (∑ j : Fin n,
        (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
          |x j|) +
        |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  classical
  let Ahat : Fin steps → Fin n → ℝ :=
    rowSampleLSMatrixWithBasisScale s U A samples
  let bhat : Fin steps → ℝ :=
    rowSampleLSVectorWithBasisScale s U b samples
  let Afl : Fin steps → Fin n → ℝ :=
    fl_rowSampleLSMatrixWithBasisScale fp s U A samples
  let bfl : Fin steps → ℝ :=
    fl_rowSampleLSVectorWithBasisScale fp s U b samples
  have hAerr : ∀ j : Fin n,
      |Afl t j - Ahat t j| ≤ |Ahat t j| * fp.u := by
    intro j
    exact
      fl_rowSampleLSMatrixWithBasisScale_error_bound
        fp s U A samples t j hdenom
  have hberr :
      |bfl t - bhat t| ≤ |bhat t| * fp.u :=
    fl_rowSampleLSVectorWithBasisScale_error_bound
      fp s U b samples t hdenom
  have hsumdiff :
      (∑ j : Fin n, Afl t j * x j) -
        (∑ j : Fin n, Ahat t j * x j) =
        ∑ j : Fin n, (Afl t j - Ahat t j) * x j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiff :
      lsResidual Afl bfl x t - lsResidual Ahat bhat x t =
        (∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
          (bfl t - bhat t) := by
    unfold lsResidual rectMatMulVec
    calc
      (∑ j : Fin n, Afl t j * x j) - bfl t -
          ((∑ j : Fin n, Ahat t j * x j) - bhat t)
          =
        ((∑ j : Fin n, Afl t j * x j) -
          (∑ j : Fin n, Ahat t j * x j)) -
          (bfl t - bhat t) := by
            ring
      _ = (∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
            (bfl t - bhat t) := by
            rw [hsumdiff]
  calc
    |lsResidual Afl bfl x t - lsResidual Ahat bhat x t|
        = |(∑ j : Fin n, (Afl t j - Ahat t j) * x j) -
            (bfl t - bhat t)| := by
            rw [hdiff]
    _ ≤ |∑ j : Fin n, (Afl t j - Ahat t j) * x j| +
          |bfl t - bhat t| := by
            simpa [abs_sub_comm] using
              (abs_sub_le (∑ j : Fin n, (Afl t j - Ahat t j) * x j)
                0 (bfl t - bhat t))
    _ ≤ (∑ j : Fin n, |(Afl t j - Ahat t j) * x j|) +
          |bfl t - bhat t| := by
            exact add_le_add
              (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ = (∑ j : Fin n, |Afl t j - Ahat t j| * |x j|) +
          |bfl t - bhat t| := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul (Afl t j - Ahat t j) (x j)
    _ ≤ (∑ j : Fin n, (|Ahat t j| * fp.u) * |x j|) +
          |bhat t| * fp.u := by
            apply add_le_add
            · apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_right (hAerr j) (abs_nonneg _)
            · exact hberr

/-- Support-specialized residual perturbation bound for the canonical row-trace
    law: on traces whose sampled basis rows have positive probability, the
    row-scaling denominators are nonzero and the rounded residual bound applies
    without an extra denominator premise. -/
theorem fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ) (t : Fin s)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsResidual
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x t -
      lsResidual
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x t| ≤
      (∑ j : Fin n,
        (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
          |x j|) +
        |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u := by
  exact
    fl_rowSampleLSResidualWithBasisScale_error_bound
      fp s A b U samples x t
      (rowSampleScaleDen_ne_zero s U (samples t) hs (hprob t))

/-- Generic deterministic lift from a residual-vector perturbation to a
    squared least-squares objective perturbation. -/
theorem lsObjective_residual_difference_bound
    {m n : ℕ}
    (Aexact Apert : Fin m → Fin n → ℝ)
    (bexact bpert : Fin m → ℝ) (x : Fin n → ℝ) :
    |lsObjective Apert bpert x - lsObjective Aexact bexact x| ≤
      2 * vecNorm2 (lsResidual Aexact bexact x) *
          vecNorm2 (fun i : Fin m =>
            lsResidual Apert bpert x i - lsResidual Aexact bexact x i) +
        vecNorm2Sq (fun i : Fin m =>
          lsResidual Apert bpert x i - lsResidual Aexact bexact x i) := by
  let r : Fin m → ℝ := lsResidual Aexact bexact x
  let e : Fin m → ℝ := fun i =>
    lsResidual Apert bpert x i - lsResidual Aexact bexact x i
  have hres : lsResidual Apert bpert x = fun i : Fin m => r i + e i := by
    ext i
    simp [r, e]
  unfold lsObjective
  rw [hres]
  simpa [r, e] using abs_vecNorm2Sq_add_sub_le r e

/-- Budgeted deterministic lift from entrywise residual perturbations to a
    squared least-squares objective perturbation. -/
theorem lsObjective_residual_budget_bound
    {m n : ℕ}
    (Aexact Apert : Fin m → Fin n → ℝ)
    (bexact bpert : Fin m → ℝ) (x : Fin n → ℝ)
    (budget : Fin m → ℝ)
    (hbudget : ∀ i : Fin m,
      |lsResidual Apert bpert x i - lsResidual Aexact bexact x i| ≤ budget i) :
    |lsObjective Apert bpert x - lsObjective Aexact bexact x| ≤
      2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget +
        vecNorm2Sq budget := by
  let e : Fin m → ℝ := fun i =>
    lsResidual Apert bpert x i - lsResidual Aexact bexact x i
  have hbase :=
    lsObjective_residual_difference_bound Aexact Apert bexact bpert x
  have he_norm : vecNorm2 e ≤ vecNorm2 budget := by
    exact vecNorm2_le_of_abs_le e budget hbudget
  have he_sq : vecNorm2Sq e ≤ vecNorm2Sq budget := by
    exact vecNorm2Sq_le_of_abs_le e budget hbudget
  have hcoef_nonneg :
      0 ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) := by
    exact mul_nonneg (by norm_num) (vecNorm2_nonneg _)
  have hterm :
      2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 e ≤
        2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget := by
    exact mul_le_mul_of_nonneg_left he_norm hcoef_nonneg
  calc
    |lsObjective Apert bpert x - lsObjective Aexact bexact x|
        ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 e +
            vecNorm2Sq e := hbase
    _ ≤ 2 * vecNorm2 (lsResidual Aexact bexact x) * vecNorm2 budget +
          vecNorm2Sq budget := by
          exact add_le_add hterm he_sq

/-- Residual budget induced by a componentwise forward-error bound on the
    least-squares solution vector. -/
noncomputable def lsSolutionForwardResidualBudget {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (dx : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, |A i j| * dx j

/-- Objective gap induced by a componentwise forward-error bound on a vector
    near an exact least-squares minimizer. -/
noncomputable def lsSolutionForwardObjectiveGap {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xStar : Fin n → ℝ) (dx : Fin n → ℝ) : ℝ :=
  2 * vecNorm2 (lsResidual A b xStar) *
      vecNorm2 (lsSolutionForwardResidualBudget A dx) +
    vecNorm2Sq (lsSolutionForwardResidualBudget A dx)

/-- A componentwise solution-vector error bound induces a rowwise residual
    perturbation bound. -/
theorem lsResidual_difference_bound_of_solution_abs_le
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (_hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j)
    (i : Fin m) :
    |lsResidual A b xHat i - lsResidual A b xStar i| ≤
      lsSolutionForwardResidualBudget A dx i := by
  have hdiff :
      lsResidual A b xHat i - lsResidual A b xStar i =
        ∑ j : Fin n, A i j * (xHat j - xStar j) := by
    unfold lsResidual rectMatMulVec
    calc
      (∑ j : Fin n, A i j * xHat j) - b i -
          ((∑ j : Fin n, A i j * xStar j) - b i)
          = (∑ j : Fin n, A i j * xHat j) -
              (∑ j : Fin n, A i j * xStar j) := by ring
      _ = ∑ j : Fin n, (A i j * xHat j - A i j * xStar j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin n, A i j * (xHat j - xStar j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
  calc
    |lsResidual A b xHat i - lsResidual A b xStar i|
        = |∑ j : Fin n, A i j * (xHat j - xStar j)| := by
            rw [hdiff]
    _ ≤ ∑ j : Fin n, |A i j * (xHat j - xStar j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |xHat j - xStar j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
    _ ≤ ∑ j : Fin n, |A i j| * dx j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hclose j) (abs_nonneg _)
    _ = lsSolutionForwardResidualBudget A dx i := rfl

/-- Objective perturbation bound induced by a componentwise solution-vector
    forward-error certificate. -/
theorem lsObjective_solution_forward_error_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j) :
    |lsObjective A b xHat - lsObjective A b xStar| ≤
      lsSolutionForwardObjectiveGap A b xStar dx := by
  let e : Fin m → ℝ := fun i =>
    lsResidual A b xHat i - lsResidual A b xStar i
  have hres :
      lsResidual A b xHat =
        fun i : Fin m => lsResidual A b xStar i + e i := by
    ext i
    simp [e]
  have hbase :
      |vecNorm2Sq (fun i : Fin m => lsResidual A b xStar i + e i) -
          vecNorm2Sq (lsResidual A b xStar)| ≤
        2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e +
          vecNorm2Sq e :=
    abs_vecNorm2Sq_add_sub_le (lsResidual A b xStar) e
  have he_budget : ∀ i : Fin m,
      |e i| ≤ lsSolutionForwardResidualBudget A dx i := by
    intro i
    exact
      lsResidual_difference_bound_of_solution_abs_le
        A b xHat xStar dx hdx hclose i
  have he_norm :
      vecNorm2 e ≤ vecNorm2 (lsSolutionForwardResidualBudget A dx) :=
    vecNorm2_le_of_abs_le e (lsSolutionForwardResidualBudget A dx) he_budget
  have he_sq :
      vecNorm2Sq e ≤ vecNorm2Sq (lsSolutionForwardResidualBudget A dx) :=
    vecNorm2Sq_le_of_abs_le e (lsSolutionForwardResidualBudget A dx) he_budget
  have hcoef_nonneg :
      0 ≤ 2 * vecNorm2 (lsResidual A b xStar) := by
    exact mul_nonneg (by norm_num) (vecNorm2_nonneg _)
  have hterm :
      2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e ≤
        2 * vecNorm2 (lsResidual A b xStar) *
          vecNorm2 (lsSolutionForwardResidualBudget A dx) := by
    exact mul_le_mul_of_nonneg_left he_norm hcoef_nonneg
  unfold lsObjective
  calc
    |vecNorm2Sq (lsResidual A b xHat) -
        vecNorm2Sq (lsResidual A b xStar)|
        = |vecNorm2Sq (fun i : Fin m => lsResidual A b xStar i + e i) -
            vecNorm2Sq (lsResidual A b xStar)| := by
            rw [hres]
    _ ≤ 2 * vecNorm2 (lsResidual A b xStar) * vecNorm2 e +
          vecNorm2Sq e := hbase
    _ ≤ 2 * vecNorm2 (lsResidual A b xStar) *
            vecNorm2 (lsSolutionForwardResidualBudget A dx) +
          vecNorm2Sq (lsSolutionForwardResidualBudget A dx) := by
          exact add_le_add hterm he_sq

/-- A componentwise forward-error certificate relative to an exact minimizer
    gives an additive-gap approximate minimizer. -/
theorem isLeastSquaresApproxMinimizer_of_solution_abs_le
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (xHat xStar dx : Fin n → ℝ)
    (hstar : IsLeastSquaresMinimizer A b xStar)
    (hdx : ∀ j : Fin n, 0 ≤ dx j)
    (hclose : ∀ j : Fin n, |xHat j - xStar j| ≤ dx j) :
    IsLeastSquaresApproxMinimizer A b xHat
      (lsSolutionForwardObjectiveGap A b xStar dx) := by
  intro y
  have hdiff :=
    lsObjective_solution_forward_error_bound A b xHat xStar dx hdx hclose
  have hupper :
      lsObjective A b xHat ≤
        lsObjective A b xStar +
          lsSolutionForwardObjectiveGap A b xStar dx := by
    have h := (abs_le.mp hdiff).2
    linarith
  have hmin := hstar y
  linarith

/-- Componentwise solution certificate induced by a perturbed normal-equation
    system and the local Gram forward-error theorem. -/
noncomputable def gramForwardSolverDx {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (εG εg : ℝ)
    (xHat : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    ∑ j : Fin n, |ATA_inv i j| *
      (εG * ∑ k : Fin n, |xHat k| + εg)

/-- The Gram-system forward-error certificate is nonnegative when its scalar
    perturbation radii are nonnegative. -/
theorem gramForwardSolverDx_nonneg {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (εG εg : ℝ)
    (xHat : Fin n → ℝ)
    (hεG : 0 ≤ εG) (hεg : 0 ≤ εg) :
    ∀ i : Fin n, 0 ≤ gramForwardSolverDx ATA_inv εG εg xHat i := by
  intro i
  unfold gramForwardSolverDx
  apply Finset.sum_nonneg
  intro j _
  exact
    mul_nonneg (abs_nonneg _) (add_nonneg
      (mul_nonneg hεG (Finset.sum_nonneg fun k _ => abs_nonneg _))
      hεg)

/-- A perturbed normal-equation solve supplies the componentwise certificate
    used by the literal rounded sampled-row solver theorem.

This is a small adapter around the repository's `gram_forward_error_normwise`:
it does not assert that a particular QR or preconditioner produces the
perturbed system; it converts such a proved perturbed-system certificate into
the `solverDx` shape needed by the RandNLA objective transfer. -/
theorem gram_forward_error_certificate_of_perturbed_gram_system {n : ℕ}
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb xStar xHat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA xStar i = ATb i)
    (ΔG : Fin n → Fin n → ℝ) (Δg : Fin n → ℝ)
    (hPerturbed : ∀ i,
      matMulVec n (fun a b => ATA a b + ΔG a b) xHat i =
        ATb i + Δg i)
    (εG εg : ℝ)
    (hΔG_bound : ∀ i j, |ΔG i j| ≤ εG)
    (hΔg_bound : ∀ i, |Δg i| ≤ εg)
    (hεG : 0 ≤ εG) (hεg : 0 ≤ εg) :
    ∀ i : Fin n,
      |xHat i - xStar i| ≤
        gramForwardSolverDx ATA_inv εG εg xHat i := by
  exact
    gram_forward_error_normwise n ATA ATA_inv hInv ATb xStar xHat
      hExact ΔG Δg hPerturbed hΔG_bound hΔg_bound hεG hεg

/-- Componentwise solver certificate induced by the local
    `LSQRSolveBackwardError` structure.  The Frobenius bound on `ΔG` is
    converted entrywise using `abs_entry_le_frobNorm`; the right-hand-side
    radius is defensively replaced by `max c_g 0`, so no separate
    nonnegativity hypothesis on `c_g` is needed. -/
noncomputable def lsQRSolveBackwardSolverDx {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (c_G c_g : ℝ)
    (xHat : Fin n → ℝ) : Fin n → ℝ :=
  gramForwardSolverDx ATA_inv c_G (max c_g 0) xHat

/-- The solver certificate extracted from `LSQRSolveBackwardError` is
    nonnegative. -/
theorem lsQRSolveBackwardSolverDx_nonneg {n : ℕ}
    (ATA_inv : Fin n → Fin n → ℝ) (c_G c_g : ℝ)
    (xHat : Fin n → ℝ) (hcG : 0 ≤ c_G) :
    ∀ i : Fin n, 0 ≤ lsQRSolveBackwardSolverDx ATA_inv c_G c_g xHat i := by
  intro i
  unfold lsQRSolveBackwardSolverDx
  exact
    gramForwardSolverDx_nonneg ATA_inv c_G (max c_g 0) xHat
      hcG (le_max_right c_g 0) i

/-- A local QR least-squares backward-error specification supplies the
    componentwise forward-error certificate used by the RandNLA objective
    transfer.  This is still a spec adapter: it does not prove that a concrete
    QR implementation establishes `LSQRSolveBackwardError`. -/
theorem gram_forward_error_certificate_of_ls_qr_solve_backward_error {n : ℕ}
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n ATA ATA_inv)
    (ATb xStar xHat : Fin n → ℝ)
    (hExact : ∀ i, matMulVec n ATA xStar i = ATb i)
    (c_G c_g : ℝ)
    (hBack : LSQRSolveBackwardError n ATA ATb xHat c_G c_g) :
    ∀ i : Fin n,
      |xHat i - xStar i| ≤
        lsQRSolveBackwardSolverDx ATA_inv c_G c_g xHat i := by
  rcases hBack.result with ⟨ΔG, Δg, hPerturbed, hΔG_frob, hΔg_bound⟩
  have hcG : 0 ≤ c_G := le_trans (frobNorm_nonneg ΔG) hΔG_frob
  unfold lsQRSolveBackwardSolverDx
  exact
    gram_forward_error_certificate_of_perturbed_gram_system
      ATA ATA_inv hInv ATb xStar xHat hExact ΔG Δg hPerturbed
      c_G (max c_g 0)
      (fun i j => le_trans (abs_entry_le_frobNorm ΔG i j) hΔG_frob)
      (fun i => le_trans (hΔg_bound i) (le_max_left c_g 0))
      hcG (le_max_right c_g 0)

/-- Entrywise budget for the literal rounded sampled/scaled least-squares
    residual. -/
noncomputable def rowSampleLSResidualFpBudget
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) : Fin steps → ℝ :=
  fun t =>
    (∑ j : Fin n,
      (|rowSampleLSMatrixWithBasisScale s U A samples t j| * fp.u) *
        |x j|) +
      |rowSampleLSVectorWithBasisScale s U b samples t| * fp.u

/-- The rounded sampled residual budget is entrywise nonnegative. -/
theorem rowSampleLSResidualFpBudget_nonneg
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) :
    ∀ t : Fin steps,
      0 ≤ rowSampleLSResidualFpBudget fp s A b U samples x t := by
  intro t
  unfold rowSampleLSResidualFpBudget
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (mul_nonneg (abs_nonneg _) fp.u_nonneg)
      (abs_nonneg _)
  · exact mul_nonneg (abs_nonneg _) fp.u_nonneg

/-- Objective-level budget induced by the literal rounded sampled/scaled
    least-squares residual budget. -/
noncomputable def rowSampleLSObjectiveFpBudget
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) : ℝ :=
  2 *
      vecNorm2
        (lsResidual
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples) x) *
      vecNorm2 (rowSampleLSResidualFpBudget fp s A b U samples x) +
    vecNorm2Sq (rowSampleLSResidualFpBudget fp s A b U samples x)

/-- The literal rounded sampled least-squares objective budget is
    nonnegative. -/
theorem rowSampleLSObjectiveFpBudget_nonneg
    (fp : FPModel) {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (x : Fin n → ℝ) :
    0 ≤ rowSampleLSObjectiveFpBudget fp s A b U samples x := by
  unfold rowSampleLSObjectiveFpBudget
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (vecNorm2_nonneg
          (lsResidual
            (rowSampleLSMatrixWithBasisScale s U A samples)
            (rowSampleLSVectorWithBasisScale s U b samples) x)))
      (vecNorm2_nonneg
        (rowSampleLSResidualFpBudget fp s A b U samples x))
  · exact vecNorm2Sq_nonneg _

/-- Objective-level perturbation bound for the literal rounded sampled/scaled
    least-squares construction on the positive-probability support event.  This
    is the deterministic objective lift of the rowwise residual perturbation;
    a later theorem can combine it with the exact high-probability
    finite-Loewner LS event under an explicit objective budget. -/
theorem fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsObjective
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x -
      lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x| ≤
      2 *
          vecNorm2
            (lsResidual
              (rowSampleLSMatrixWithBasisScale s U A samples)
              (rowSampleLSVectorWithBasisScale s U b samples) x) *
          vecNorm2 (rowSampleLSResidualFpBudget fp s A b U samples x) +
        vecNorm2Sq (rowSampleLSResidualFpBudget fp s A b U samples x) := by
  apply
    lsObjective_residual_budget_bound
      (rowSampleLSMatrixWithBasisScale s U A samples)
      (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
      (rowSampleLSVectorWithBasisScale s U b samples)
      (fl_rowSampleLSVectorWithBasisScale fp s U b samples)
      x
      (rowSampleLSResidualFpBudget fp s A b U samples x)
  · intro t
    unfold rowSampleLSResidualFpBudget
    exact
      fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb
        fp A b U samples x t hs hprob

/-- Named-budget form of
    `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb`. -/
theorem fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget
    (fp : FPModel) {m n d s : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m s)
    (x : Fin n → ℝ)
    (hs : 0 < (s : ℝ))
    (hprob : rowTracePositiveProb U samples) :
    |lsObjective
        (fl_rowSampleLSMatrixWithBasisScale fp s U A samples)
        (fl_rowSampleLSVectorWithBasisScale fp s U b samples) x -
      lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x| ≤
      rowSampleLSObjectiveFpBudget fp s A b U samples x := by
  simpa [rowSampleLSObjectiveFpBudget] using
    fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb
      fp A b U samples x hs hprob

/-- Residual coordinates in an orthonormal-column basis `U`.

For a residual vector `r = A x - b`, this is the coefficient vector `Uᵀ r`.
When `r` lies in the column span of `U`, orthonormality gives
`r = U (Uᵀ r)`. -/
noncomputable def residualCoordinates {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun a => ∑ i : Fin m, U i a * lsResidual A b x i

/-- Every least-squares residual lies in the column span of `U`, expressed via
    the canonical orthonormal-basis coordinates `Uᵀ(Ax-b)`. -/
def ResidualsInColumnSpace {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, ∀ i : Fin m,
    lsResidual A b x i =
      ∑ a : Fin d, U i a * residualCoordinates A b U x a

/-- A supplied coordinate representation of the data columns and the right-hand
    side in the columns of `U`. -/
def ColumnsAndRhsInColumnSpace {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ) : Prop :=
  (∀ i : Fin m, ∀ j : Fin n,
    A i j = ∑ a : Fin d, U i a * Acoord j a) ∧
  (∀ i : Fin m, b i = ∑ a : Fin d, U i a * bcoord a)

/-- Residual coordinates induced by coordinate representations of the columns
    of `A` and the vector `b`. -/
noncomputable def residualCoordinatesFromColumns {n d : ℕ}
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (x : Fin n → ℝ) : Fin d → ℝ :=
  fun a => ∑ j : Fin n, Acoord j a * x j - bcoord a

/-- If a residual has any coordinates in an orthonormal-column basis, then the
    canonical coordinates `Uᵀr` reconstruct the same residual. -/
theorem residualsInColumnSpace_of_residual_representation
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a) :
    ResidualsInColumnSpace A b U := by
  have hcoord :
      ∀ x : Fin n → ℝ, residualCoordinates A b U x = coord x := by
    intro x
    ext a
    unfold residualCoordinates
    simp_rw [hres x]
    calc
      ∑ i : Fin m, U i a * (∑ c : Fin d, U i c * coord x c)
          = ∑ c : Fin d, (∑ i : Fin m, U i a * U i c) * coord x c := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro c _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ c : Fin d, (if a = c then 1 else 0) * coord x c := by
              apply Finset.sum_congr rfl
              intro c _
              rw [hU a c]
      _ = coord x a := by
              simp [Finset.mem_univ]
  intro x i
  rw [hcoord x]
  exact hres x i

/-- Column-coordinate representations for `A` and `b` induce a residual
    coordinate representation for every `A x - b`. -/
theorem lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (hcols : ColumnsAndRhsInColumnSpace A b U Acoord bcoord)
    (x : Fin n → ℝ) (i : Fin m) :
    lsResidual A b x i =
      ∑ a : Fin d, U i a *
        residualCoordinatesFromColumns Acoord bcoord x a := by
  have hA := hcols.1
  have hb := hcols.2
  unfold lsResidual rectMatMulVec residualCoordinatesFromColumns
  calc
    ∑ j : Fin n, A i j * x j - b i
        = ∑ j : Fin n, (∑ a : Fin d, U i a * Acoord j a) * x j -
            ∑ a : Fin d, U i a * bcoord a := by
            rw [hb i]
            apply congrArg₂ Sub.sub
            · apply Finset.sum_congr rfl
              intro j _
              rw [hA i j]
            · rfl
    _ = ∑ a : Fin d, U i a *
          (∑ j : Fin n, Acoord j a * x j - bcoord a) := by
            calc
              ∑ j : Fin n, (∑ a : Fin d, U i a * Acoord j a) * x j -
                  ∑ a : Fin d, U i a * bcoord a
                  =
                (∑ a : Fin d, U i a *
                  ∑ j : Fin n, Acoord j a * x j) -
                  ∑ a : Fin d, U i a * bcoord a := by
                    apply congrArg₂ Sub.sub
                    · simp_rw [Finset.sum_mul]
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
                    · rfl
              _ = ∑ a : Fin d, U i a *
                    (∑ j : Fin n, Acoord j a * x j - bcoord a) := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring

/-- If the columns of `A` and the right-hand side `b` lie in an
    orthonormal-column basis `U`, then every least-squares residual lies in the
    column span of `U`. -/
theorem residualsInColumnSpace_of_columnsAndRhsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (Acoord : Fin n → Fin d → ℝ) (bcoord : Fin d → ℝ)
    (hcols : ColumnsAndRhsInColumnSpace A b U Acoord bcoord) :
    ResidualsInColumnSpace A b U := by
  exact
    residualsInColumnSpace_of_residual_representation
      A b U hU (residualCoordinatesFromColumns Acoord bcoord)
      (fun x i =>
        lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace
          A b U Acoord bcoord hcols x i)

/-- Embed a finite real coordinate vector into Mathlib's Euclidean-space type.

The RandNLA files use plain functions `Fin m → ℝ` for matrices and vectors,
while Mathlib's orthonormal-basis API uses `EuclideanSpace ℝ (Fin m)`.  This
small bridge lets us reuse Mathlib's finite-dimensional orthonormal-basis
construction without changing the algorithm-facing definitions. -/
noncomputable def euclideanVec {m : ℕ} (v : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 v

@[simp]
theorem euclideanVec_apply {m : ℕ} (v : Fin m → ℝ) (i : Fin m) :
    euclideanVec v i = v i := rfl

/-- The augmented least-squares data vectors: all columns of `A` and the
right-hand side `b`, viewed as vectors in `ℝ^m`. -/
noncomputable def augmentedDataVector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Sum (Fin n) Unit → EuclideanSpace ℝ (Fin m)
  | Sum.inl j => euclideanVec (fun i => A i j)
  | Sum.inr _ => euclideanVec b

/-- The finite-dimensional augmented data span `span{columns(A), b}`. -/
noncomputable def augmentedDataSpan {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range (augmentedDataVector A b))

/-- Every augmented data vector belongs to the augmented data span. -/
theorem augmentedDataVector_mem_span {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (c : Sum (Fin n) Unit) :
    augmentedDataVector A b c ∈ augmentedDataSpan A b := by
  exact Submodule.subset_span (Set.mem_range_self c)

/-- The orthonormal-column matrix obtained by choosing Mathlib's standard
orthonormal basis of the augmented data span.  Its number of columns is the
rank/dimension of `span{columns(A), b}`. -/
noncomputable def augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin m → Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun i a =>
    (((stdOrthonormalBasis ℝ (augmentedDataSpan A b) a :
      augmentedDataSpan A b) : EuclideanSpace ℝ (Fin m)) i)

/-- Coordinates of the columns of `A` in the augmented-span orthonormal basis. -/
noncomputable def augmentedSpanColumnCoords {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin n → Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun j a =>
    (stdOrthonormalBasis ℝ (augmentedDataSpan A b)).repr
      ⟨augmentedDataVector A b (Sum.inl j),
        augmentedDataVector_mem_span A b (Sum.inl j)⟩ a

/-- Coordinates of `b` in the augmented-span orthonormal basis. -/
noncomputable def augmentedSpanRhsCoords {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    Fin (Module.finrank ℝ (augmentedDataSpan A b)) → ℝ :=
  fun a =>
    (stdOrthonormalBasis ℝ (augmentedDataSpan A b)).repr
      ⟨augmentedDataVector A b (Sum.inr ()),
        augmentedDataVector_mem_span A b (Sum.inr ())⟩ a

/-- The augmented-span basis matrix has orthonormal columns. -/
theorem hasOrthonormalColumns_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    HasOrthonormalColumns (augmentedSpanBasisMatrix A b) := by
  intro j k
  let S := augmentedDataSpan A b
  let B := stdOrthonormalBasis ℝ S
  have h := B.inner_eq_ite j k
  rw [Submodule.coe_inner, PiLp.inner_apply] at h
  calc
    ∑ i : Fin m,
        augmentedSpanBasisMatrix A b i j *
          augmentedSpanBasisMatrix A b i k
        = ∑ i : Fin m,
            inner ℝ
              (((B j : S) : EuclideanSpace ℝ (Fin m)) i)
              (((B k : S) : EuclideanSpace ℝ (Fin m)) i) := by
            apply Finset.sum_congr rfl
            intro i _
            change
              augmentedSpanBasisMatrix A b i j *
                  augmentedSpanBasisMatrix A b i k =
                RCLike.re
                  ((((B k : S) : EuclideanSpace ℝ (Fin m)) i) *
                    (starRingEnd ℝ)
                      (((B j : S) : EuclideanSpace ℝ (Fin m)) i))
            simp [augmentedSpanBasisMatrix, S, B, mul_comm]
    _ = if j = k then (1 : ℝ) else 0 := h

/-- The augmented-span orthonormal basis represents every column of `A` and the
right-hand side `b`. -/
theorem columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ColumnsAndRhsInColumnSpace A b
      (augmentedSpanBasisMatrix A b)
      (augmentedSpanColumnCoords A b)
      (augmentedSpanRhsCoords A b) := by
  constructor
  · intro i j
    let S := augmentedDataSpan A b
    let B := stdOrthonormalBasis ℝ S
    let x : S :=
      ⟨augmentedDataVector A b (Sum.inl j),
        augmentedDataVector_mem_span A b (Sum.inl j)⟩
    have hsum := B.sum_repr x
    have hi :=
      congrArg (fun v : S => ((v : EuclideanSpace ℝ (Fin m)) i)) hsum
    symm
    simpa [augmentedSpanBasisMatrix, augmentedSpanColumnCoords,
      augmentedDataVector, euclideanVec, S, B, x, Pi.smul_apply,
      smul_eq_mul, mul_comm] using hi
  · intro i
    let S := augmentedDataSpan A b
    let B := stdOrthonormalBasis ℝ S
    let x : S :=
      ⟨augmentedDataVector A b (Sum.inr ()),
        augmentedDataVector_mem_span A b (Sum.inr ())⟩
    have hsum := B.sum_repr x
    have hi :=
      congrArg (fun v : S => ((v : EuclideanSpace ℝ (Fin m)) i)) hsum
    symm
    simpa [augmentedSpanBasisMatrix, augmentedSpanRhsCoords,
      augmentedDataVector, euclideanVec, S, B, x, Pi.smul_apply,
      smul_eq_mul, mul_comm] using hi

/-- Every least-squares residual lies in the augmented data span basis. -/
theorem residualsInColumnSpace_augmentedSpanBasisMatrix {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ResidualsInColumnSpace A b (augmentedSpanBasisMatrix A b) := by
  exact
    residualsInColumnSpace_of_columnsAndRhsInColumnSpace
      A b (augmentedSpanBasisMatrix A b)
      (hasOrthonormalColumns_augmentedSpanBasisMatrix A b)
      (augmentedSpanColumnCoords A b)
      (augmentedSpanRhsCoords A b)
      (columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix A b)

/-- The square identity matrix has orthonormal columns. -/
theorem hasOrthonormalColumns_idMatrix (m : ℕ) :
    HasOrthonormalColumns (idMatrix m) := by
  intro j k
  unfold idMatrix
  by_cases hjk : j = k
  · subst k
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  · calc
      (∑ i : Fin m, (if i = j then (1 : ℝ) else 0) *
          (if i = k then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hij : i = j
        · simp [hij, hjk]
        · simp [hij]
      _ = (if j = k then (1 : ℝ) else 0) := by
        simp [hjk]

/-- Canonical residual coordinates in the full identity basis are just the
    residual vector itself. -/
theorem residualCoordinates_idMatrix
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    residualCoordinates A b (idMatrix m) x = lsResidual A b x := by
  ext a
  simp [residualCoordinates, idMatrix, eq_comm]

/-- The identity basis contains every least-squares residual.  This is the
    full-row-space fallback basis for equation (6): it is not the sharp
    low-dimensional leverage basis, but it discharges the column-space
    hypothesis without any SVD/QR infrastructure. -/
theorem residualsInColumnSpace_idMatrix
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    ResidualsInColumnSpace A b (idMatrix m) := by
  intro x i
  have hid := congrFun (idMatrix_mulVec m (lsResidual A b x)) i
  rw [residualCoordinates_idMatrix A b x]
  exact hid.symm

/-- If all residuals lie in the column span of an orthonormal-column matrix
    `U`, then the original least-squares objective is exactly the squared norm
    of the canonical residual-coordinate vector. -/
theorem lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace
    {m n d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (hU : HasOrthonormalColumns U)
    (hcol : ResidualsInColumnSpace A b U)
    (x : Fin n → ℝ) :
    lsObjective A b x = vecNorm2Sq (residualCoordinates A b U x) := by
  let c : Fin d → ℝ := residualCoordinates A b U x
  have hres :
      lsResidual A b x =
        fun i : Fin m => ∑ a : Fin d, U i a * c a := by
    ext i
    exact hcol x i
  have hgram : rowSketchGram U = idMatrix d := by
    ext j k
    exact hU j k
  calc
    lsObjective A b x = vecNorm2Sq (lsResidual A b x) := rfl
    _ = vecNorm2Sq
        (fun i : Fin m => ∑ a : Fin d, U i a * c a) := by
          rw [hres]
    _ = ∑ a : Fin d, c a * matMulVec d (rowSketchGram U) c a := by
          exact
            vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
              U c
    _ = ∑ a : Fin d, c a * matMulVec d (idMatrix d) c a := by
          rw [hgram]
    _ = vecNorm2Sq c := quadraticForm_idMatrix_eq_vecNorm2Sq c















































/-- Concrete objective representation for a row-sampled least-squares sketch
    scaled by leverage probabilities from a basis matrix `U`.

If every original residual has coordinates `coord x` in the rows of `U`, then
the sampled objective is exactly the coordinate norm plus the quadratic form of
the sampled Gram error `ŨᵀŨ - I`.  This is the missing algebraic link between
the Algorithm 2 equation (7) Gram event and the equation (8) least-squares
objective bridge. -/
theorem rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error
    {m n d steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (U : Fin m → Fin d → ℝ) (samples : RowTrace m steps)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (hres : ∀ x : Fin n → ℝ, ∀ i : Fin m,
      lsResidual A b x i = ∑ a : Fin d, U i a * coord x a)
    (x : Fin n → ℝ) :
    lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x =
      vecNorm2Sq (coord x) +
        ∑ j : Fin d, coord x j *
          matMulVec d
            (fun j k => rowSampleGram s U samples j k - idMatrix d j k)
            (coord x) j := by
  let y : Fin d → ℝ := coord x
  have hresidual :
      lsResidual
          (rowSampleLSMatrixWithBasisScale s U A samples)
          (rowSampleLSVectorWithBasisScale s U b samples) x =
        fun t : Fin steps =>
          ∑ a : Fin d, rowSampleSketch s U samples t a * y a := by
    ext t
    exact rowSampleLSResidualWithBasisScale_eq_coord
      s A b U samples coord hres x t
  calc
    lsObjective
        (rowSampleLSMatrixWithBasisScale s U A samples)
        (rowSampleLSVectorWithBasisScale s U b samples) x
        = vecNorm2Sq
            (fun t : Fin steps =>
              ∑ a : Fin d, rowSampleSketch s U samples t a * y a) := by
            unfold lsObjective
            rw [hresidual]
    _ = ∑ j : Fin d, y j * matMulVec d (rowSampleGram s U samples) y j := by
            exact
              vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram
                s U samples y
    _ = vecNorm2Sq y +
        ∑ j : Fin d, y j *
          matMulVec d
            (fun j k => rowSampleGram s U samples j k - idMatrix d j k) y j := by
            rw [← vecNorm2Sq_add_quadraticForm_sub_id_eq_quadraticForm
              (rowSampleGram s U samples) y]

/-- A coordinate-space quadratic-form error implies residual-objective
    preservation.

This is the deterministic algebraic bridge used by subspace-embedding
arguments.  The map `coord` represents each original residual in an
orthonormal coordinate system, so `horig` states that the original objective is
`||coord x||₂²`.  The sketched objective is allowed to differ by the quadratic
form `coord(x)ᵀ E coord(x)`.  If `E` has operator-2 norm at most `ε`, then the
sketch preserves every squared residual objective within `1 ± ε`.

The theorem does not prove that a random sketch produces such an `E`; it is the
deterministic bridge that a later randomized subspace-embedding theorem can
compose with. -/
theorem preservesLSObjective_of_coordinate_quadratic_error
    {m n r d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Fin d → Fin d → ℝ) {ε : ℝ}
    (_hε_nonneg : 0 ≤ ε)
    (hE : opNorm2Le E ε)
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ x : Fin n → ℝ,
      lsObjective SA Sb x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d E (coord x) j) :
    PreservesLSObjective A b SA Sb ε := by
  intro x
  let y : Fin d → ℝ := coord x
  have hquad_abs :
      |∑ j : Fin d, y j * matMulVec d E y j| ≤ ε * vecNorm2Sq y :=
    abs_vecInnerProduct_matMulVec_le_of_opNorm2Le E hE y
  have hquad_lower :
      -(ε * vecNorm2Sq y) ≤
        ∑ j : Fin d, y j * matMulVec d E y j :=
    (abs_le.mp hquad_abs).1
  have hquad_upper :
      ∑ j : Fin d, y j * matMulVec d E y j ≤ ε * vecNorm2Sq y :=
    (abs_le.mp hquad_abs).2
  have hnorm_nonneg : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  constructor
  · rw [horig x, hsketch x]
    change (1 - ε) * vecNorm2Sq y ≤
      vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j
    nlinarith
  · rw [horig x, hsketch x]
    change vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j ≤
      (1 + ε) * vecNorm2Sq y
    nlinarith

/-- High-probability transfer version of
    `preservesLSObjective_of_coordinate_quadratic_error`.

If a probability theorem already proves that the random coordinate-space Gram
error `E ω` has operator-2 norm at most `ε`, and each outcome has the stated
coordinate/quadratic representation, then the same probability lower bound
holds for the least-squares preservation event.  This theorem is deliberately
only a transfer: the probability bound `hprob` must come from a separately
proved concentration result. -/
theorem eventProb_preservesLSObjective_of_coordinate_quadratic_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ) {ε α : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hprob : α ≤ P.eventProb {ω | opNorm2Le (E ω) ε})
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
  have hsubset :
      {ω | opNorm2Le (E ω) ε} ⊆
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
    intro ω hE
    exact preservesLSObjective_of_coordinate_quadratic_error
      A b (SA ω) (Sb ω) coord (E ω) hε_nonneg hE horig
      (hsketch ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- A coordinate-space two-sided finite-Loewner event implies residual-objective
    preservation.

This is the sharper analogue of
`preservesLSObjective_of_coordinate_quadratic_error`: instead of first
converting to an operator-norm bound, it consumes the exact two-sided Loewner
event produced by the Bennett route for leverage-score row sampling. -/
theorem preservesLSObjective_of_coordinate_finiteLoewner_error
    {m n r d : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Fin d → Fin d → ℝ) {ε : ℝ}
    (hUpper :
      finiteLoewnerLe E
        (fun j k : Fin d => ε * finiteIdMatrix j k))
    (hLower :
      finiteLoewnerLe (fun j k : Fin d => -E j k)
        (fun j k : Fin d => ε * finiteIdMatrix j k))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ x : Fin n → ℝ,
      lsObjective SA Sb x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d E (coord x) j) :
    PreservesLSObjective A b SA Sb ε := by
  intro x
  let y : Fin d → ℝ := coord x
  have hquad_abs :
      |∑ j : Fin d, y j * matMulVec d E y j| ≤ ε * vecNorm2Sq y := by
    have hfinite :=
      abs_finiteQuadraticForm_le_of_loewnerLe_neg
        E hUpper hLower y
    simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
      finiteVecNorm2Sq_fin] using hfinite
  have hquad_lower :
      -(ε * vecNorm2Sq y) ≤
        ∑ j : Fin d, y j * matMulVec d E y j :=
    (abs_le.mp hquad_abs).1
  have hquad_upper :
      ∑ j : Fin d, y j * matMulVec d E y j ≤ ε * vecNorm2Sq y :=
    (abs_le.mp hquad_abs).2
  have hnorm_nonneg : 0 ≤ vecNorm2Sq y := vecNorm2Sq_nonneg y
  constructor
  · rw [horig x, hsketch x]
    change (1 - ε) * vecNorm2Sq y ≤
      vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j
    nlinarith
  · rw [horig x, hsketch x]
    change vecNorm2Sq y + ∑ j : Fin d, y j * matMulVec d E y j ≤
      (1 + ε) * vecNorm2Sq y
    nlinarith

/-- Probability transfer for the coordinate-space finite-Loewner bridge. -/
theorem eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ) {ε α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)})
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
  have hsubset :
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)} ⊆
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} := by
    intro ω hE
    exact preservesLSObjective_of_coordinate_finiteLoewner_error
      A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
      (hsketch ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Least-squares objectives are nonnegative. -/
theorem lsObjective_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    0 ≤ lsObjective A b x := by
  unfold lsObjective
  exact vecNorm2Sq_nonneg _

/-- Deterministic equation (8) sketching consequence, squared-objective form.

If a sketch preserves all squared residual objectives by `1 ± ε` and `x_hat`
minimizes the sketched problem, then for every comparison vector `x_ref`,

`||A x_hat - b||₂² ≤ ((1 + ε) / (1 - ε)) ||A x_ref - b||₂²`.

The randomized theorem that a particular Algorithm 2 sketch satisfies
`PreservesLSObjective` with high probability is not assumed here and is not
proved by this theorem. -/
theorem lsObjective_le_of_sketch_preserves
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SA Sb x_hat) :
    lsObjective A b x_hat ≤
      ((1 + ε) / (1 - ε)) * lsObjective A b x_ref := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hmin := hhat x_ref
  have hupper := (hpres x_ref).2
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref :=
    le_trans hlower (le_trans hmin hupper)
  have hdiv :
      lsObjective A b x_hat ≤
        ((1 + ε) * lsObjective A b x_ref) / (1 - ε) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  have hrewrite :
      ((1 + ε) * lsObjective A b x_ref) / (1 - ε) =
        ((1 + ε) / (1 - ε)) * lsObjective A b x_ref := by
    ring
  simpa [hrewrite] using hdiv

/-- Deterministic equation (8) sketching consequence with the common
    `1 + η` target factor.

It is enough to prove
`(1 + ε) / (1 - ε) ≤ 1 + η` for the chosen embedding accuracy `ε`; this theorem
keeps that arithmetic choice explicit. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Fin r → Fin n → ℝ) (Sb : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η : ℝ}
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SA Sb x_hat) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hmain :=
    lsObjective_le_of_sketch_preserves A b SA Sb x_hat x_opt hε hpres hhat
  have hobj : 0 ≤ lsObjective A b x_opt := lsObjective_nonneg A b x_opt
  exact le_trans hmain (mul_le_mul_of_nonneg_right hfactor hobj)

/-- Deterministic transfer from an exact sketched objective to a rounded
    sketched objective with explicit additive objective-error budgets.

If `SA,Sb` preserve the original objective, `SAr,Sbr` are the rounded sketch,
and `x_hat` minimizes the rounded sketch, then the original objective at
`x_hat` is bounded by the exact-sketch factor plus the two objective
perturbation budgets: one at `x_hat` and one at the comparison vector. -/
theorem lsObjective_le_of_sketch_preserves_with_objective_error
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε τHat τRef : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SAr Sbr x_hat)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseRef :
      |lsObjective SAr Sbr x_ref - lsObjective SA Sb x_ref| ≤ τRef) :
    lsObjective A b x_hat ≤
      (((1 + ε) * lsObjective A b x_ref + τHat + τRef) /
        (1 - ε)) := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hupper := (hpres x_ref).2
  have hmin := hhat x_ref
  have hcloseHat' :
      lsObjective SA Sb x_hat ≤ lsObjective SAr Sbr x_hat + τHat := by
    have h := (abs_le.mp hcloseHat).1
    linarith
  have hcloseRef' :
      lsObjective SAr Sbr x_ref ≤ lsObjective SA Sb x_ref + τRef := by
    have h := (abs_le.mp hcloseRef).2
    linarith
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref + τHat + τRef := by
    calc
      (1 - ε) * lsObjective A b x_hat
          ≤ lsObjective SA Sb x_hat := hlower
      _ ≤ lsObjective SAr Sbr x_hat + τHat := hcloseHat'
      _ ≤ lsObjective SAr Sbr x_ref + τHat := by
            linarith
      _ ≤ lsObjective SA Sb x_ref + τRef + τHat := by
            linarith
      _ ≤ (1 + ε) * lsObjective A b x_ref + τRef + τHat := by
            linarith
      _ = (1 + ε) * lsObjective A b x_ref + τHat + τRef := by
            ring
  rw [le_div_iff₀ hpos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain

/-- `1 + η` form of
    `lsObjective_le_of_sketch_preserves_with_objective_error`.

The additive rounded-objective budgets must be small enough to fit inside the
slack between the exact sketch factor and the requested final factor.  The
hypothesis is explicit so this theorem cannot hide an unproved concentration or
perturbation estimate. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η τHat τOpt : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresMinimizer SAr Sbr x_hat)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseOpt :
      |lsObjective SAr Sbr x_opt - lsObjective SA Sb x_opt| ≤ τOpt)
    (hbudget :
      τHat + τOpt ≤
        ((1 + η) * (1 - ε) - (1 + ε)) * lsObjective A b x_opt) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hpos : 0 < 1 - ε := by linarith
  have hmain :=
    lsObjective_le_of_sketch_preserves_with_objective_error
      A b SA SAr Sb Sbr x_hat x_opt hε hpres hhat hcloseHat hcloseOpt
  refine le_trans hmain ?_
  rw [div_le_iff₀ hpos]
  nlinarith [hbudget]

/-- Deterministic transfer from an exact sketched objective to a rounded
    sketched objective with explicit additive objective-error budgets and an
    explicit solver objective gap.

This is the solver-facing version of
`lsObjective_le_of_sketch_preserves_with_objective_error`: instead of requiring
`x_hat` to be an exact minimizer of the rounded sketch, it only requires an
additive-gap approximate minimizer. -/
theorem lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_ref : Fin n → ℝ) {ε τHat τRef solverGap : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresApproxMinimizer SAr Sbr x_hat solverGap)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseRef :
      |lsObjective SAr Sbr x_ref - lsObjective SA Sb x_ref| ≤ τRef) :
    lsObjective A b x_hat ≤
      (((1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap) /
        (1 - ε)) := by
  have hpos : 0 < 1 - ε := by linarith
  have hlower := (hpres x_hat).1
  have hupper := (hpres x_ref).2
  have hmin := hhat x_ref
  have hcloseHat' :
      lsObjective SA Sb x_hat ≤ lsObjective SAr Sbr x_hat + τHat := by
    have h := (abs_le.mp hcloseHat).1
    linarith
  have hcloseRef' :
      lsObjective SAr Sbr x_ref ≤ lsObjective SA Sb x_ref + τRef := by
    have h := (abs_le.mp hcloseRef).2
    linarith
  have hchain :
      (1 - ε) * lsObjective A b x_hat ≤
        (1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap := by
    calc
      (1 - ε) * lsObjective A b x_hat
          ≤ lsObjective SA Sb x_hat := hlower
      _ ≤ lsObjective SAr Sbr x_hat + τHat := hcloseHat'
      _ ≤ lsObjective SAr Sbr x_ref + solverGap + τHat := by
            linarith
      _ ≤ lsObjective SA Sb x_ref + τRef + solverGap + τHat := by
            linarith
      _ ≤ (1 + ε) * lsObjective A b x_ref + τRef + solverGap + τHat := by
            linarith
      _ = (1 + ε) * lsObjective A b x_ref + τHat + τRef + solverGap := by
            ring
  rw [le_div_iff₀ hpos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain

/-- `1 + η` form of the rounded-objective transfer with an explicit additive
    solver objective gap.

The floating-point objective budgets and solver gap must jointly fit inside the
same slack.  This theorem is deterministic; no concentration or solver accuracy
claim is assumed implicitly. -/
theorem lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
    {m n r : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Fin r → Fin n → ℝ) (Sb Sbr : Fin r → ℝ)
    (x_hat x_opt : Fin n → ℝ) {ε η τHat τOpt solverGap : ℝ}
    (hε : ε < 1)
    (hpres : PreservesLSObjective A b SA Sb ε)
    (hhat : IsLeastSquaresApproxMinimizer SAr Sbr x_hat solverGap)
    (hcloseHat :
      |lsObjective SAr Sbr x_hat - lsObjective SA Sb x_hat| ≤ τHat)
    (hcloseOpt :
      |lsObjective SAr Sbr x_opt - lsObjective SA Sb x_opt| ≤ τOpt)
    (hbudget :
      τHat + τOpt + solverGap ≤
        ((1 + η) * (1 - ε) - (1 + ε)) * lsObjective A b x_opt) :
    lsObjective A b x_hat ≤ (1 + η) * lsObjective A b x_opt := by
  have hpos : 0 < 1 - ε := by linarith
  have hmain :=
    lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap
      A b SA SAr Sb Sbr x_hat x_opt hε hpres hhat hcloseHat hcloseOpt
  refine le_trans hmain ?_
  rw [div_le_iff₀ hpos]
  nlinarith [hbudget]

/-- Probability transfer from least-squares preservation to the randomized
    sketched-minimizer objective guarantee. -/
theorem eventProb_lsObjective_le_of_preserves
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xRef : Fin n → ℝ)
    {ε α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω)) :
    α ≤ P.eventProb
      {ω |
        lsObjective A b (xHat ω) ≤
          ((1 + ε) / (1 - ε)) * lsObjective A b xRef} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω |
          lsObjective A b (xHat ω) ≤
            ((1 + ε) / (1 - ε)) * lsObjective A b xRef} := by
    intro ω hpres
    exact lsObjective_le_of_sketch_preserves
      A b (SA ω) (Sb ω) (xHat ω) xRef hε hpres (hhat ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer from least-squares preservation to the common
    `1 + η` randomized sketched-minimizer objective guarantee. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω)) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hpres
    exact lsObjective_le_one_add_eta_of_sketch_preserves
      A b (SA ω) (Sb ω) (xHat ω) xOpt hε hfactor hpres (hhat ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched least-squares minimizers with
    explicit additive objective-error budgets.

The event must contain both the exact sketch-preservation property and the
budget inequality that absorbs the rounded-objective errors at the computed
minimizer and at `xOpt`.  This theorem is a composition rule only: it does not
prove the budget event. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hω.1 (hhat ω) (hcloseHat ω) (hcloseOpt ω) hω.2
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched minimizers when the rounded
    objective-error budget inequality is deterministic for every outcome.

This is the form used when the exact sketch-preservation event already has a
proved high-probability bound and the floating-point budget is supplied
pointwise. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_pointwise_objective_error
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε})
    (hbudget : ∀ ω,
      τHat ω + τOpt ω ≤
        ((1 + η) * (1 - ε) - (1 + ε)) *
          lsObjective A b xOpt)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω,
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hpres
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω) (hcloseOpt ω) (hbudget ω)
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched minimizers when the rounded
    objective-error bounds are only available on an auxiliary good event.

This is the support-aware version needed by literal row sampling: division
error bounds require the sampled row to have positive leverage probability, and
that condition is carried as the explicit event `Good`. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_on_event
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hpres, hbudget⟩
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Probability transfer for rounded sketched approximate minimizers when the
    rounded objective-error bounds are only available on an auxiliary good
    event and a solver objective gap is explicit. -/
theorem eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_and_solver_gap_on_event
    {Ω : Type*} [Fintype Ω] {m n r : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt solverGap : Ω → ℝ)
    {ε η α : ℝ} (hε : ε < 1)
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hhat : ∀ ω,
      IsLeastSquaresApproxMinimizer (SAr ω) (Sbr ω) (xHat ω)
        (solverGap ω))
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        PreservesLSObjective A b (SA ω) (Sb ω) ε ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hpres, hbudget⟩
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Finite-Loewner exact sketch preservation plus explicit rounded-objective
    budgets gives a high-probability rounded-minimizer objective bound.

The event carries the auxiliary good condition needed for floating-point
division support, the exact coordinate-space finite-Loewner event, and the
budget inequality that absorbs the rounded objective perturbations. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt : Ω → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hε : ε < 1)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SAr ω) (Sbr ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j)
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hE, hbudget⟩
    have hpres :
        PreservesLSObjective A b (SA ω) (Sb ω) ε :=
      preservesLSObjective_of_coordinate_finiteLoewner_error
        A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
        (hsketch ω)
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Finite-Loewner exact sketch preservation plus explicit rounded-objective
    budgets and a solver objective gap gives a high-probability approximate
    rounded-solver objective bound.

This is the solver-facing version of
`eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event`. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω) (Good : Set Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA SAr : Ω → Fin r → Fin n → ℝ)
    (Sb Sbr : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    (τHat τOpt solverGap : Ω → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt})
    (hε : ε < 1)
    (hhat : ∀ ω,
      IsLeastSquaresApproxMinimizer (SAr ω) (Sbr ω) (xHat ω)
        (solverGap ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j)
    (hcloseHat : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) (xHat ω) -
        lsObjective (SA ω) (Sb ω) (xHat ω)| ≤ τHat ω)
    (hcloseOpt : ∀ ω, ω ∈ Good →
      |lsObjective (SAr ω) (Sbr ω) xOpt -
        lsObjective (SA ω) (Sb ω) xOpt| ≤ τOpt ω) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hsubset :
      {ω |
        ω ∈ Good ∧
        (finiteLoewnerLe (E ω)
            (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin d => -E ω j k)
            (fun j k : Fin d => ε * finiteIdMatrix j k)) ∧
        τHat ω + τOpt ω + solverGap ω ≤
          ((1 + η) * (1 - ε) - (1 + ε)) *
            lsObjective A b xOpt} ⊆
        {ω | lsObjective A b (xHat ω) ≤
          (1 + η) * lsObjective A b xOpt} := by
    intro ω hω
    rcases hω with ⟨hgood, hE, hbudget⟩
    have hpres :
        PreservesLSObjective A b (SA ω) (Sb ω) ε :=
      preservesLSObjective_of_coordinate_finiteLoewner_error
        A b (SA ω) (Sb ω) coord (E ω) hE.1 hE.2 horig
        (hsketch ω)
    exact
      lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap
        A b (SA ω) (SAr ω) (Sb ω) (Sbr ω) (xHat ω) xOpt hε
        hpres (hhat ω) (hcloseHat ω hgood) (hcloseOpt ω hgood)
        hbudget
  exact hprob.trans (FiniteProbability.eventProb_mono P hsubset)

/-- A coordinate-space operator-event probability implies the randomized
    least-squares objective guarantee for the sketched minimizer. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ}
    (hε_nonneg : 0 ≤ ε)
    (hprob : α ≤ P.eventProb {ω | opNorm2Le (E ω) ε})
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hpresProb :
      α ≤ P.eventProb
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} :=
    eventProb_preservesLSObjective_of_coordinate_quadratic_error
      P A b SA Sb coord E hε_nonneg hprob horig hsketch
  exact
    eventProb_lsObjective_le_one_add_eta_of_preserves
      P A b SA Sb xHat xOpt hε hfactor hpresProb hhat

/-- A two-sided finite-Loewner coordinate-space event implies the randomized
    least-squares objective guarantee for the sketched minimizer. -/
theorem eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error
    {Ω : Type*} [Fintype Ω] {m n r d : ℕ}
    (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (SA : Ω → Fin r → Fin n → ℝ) (Sb : Ω → Fin r → ℝ)
    (coord : (Fin n → ℝ) → Fin d → ℝ)
    (E : Ω → Fin d → Fin d → ℝ)
    (xHat : Ω → Fin n → ℝ) (xOpt : Fin n → ℝ)
    {ε η α : ℝ}
    (hprob : α ≤ P.eventProb
      {ω |
        finiteLoewnerLe (E ω)
          (fun j k : Fin d => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin d => -E ω j k)
          (fun j k : Fin d => ε * finiteIdMatrix j k)})
    (hε : ε < 1)
    (hfactor : (1 + ε) / (1 - ε) ≤ 1 + η)
    (hhat : ∀ ω, IsLeastSquaresMinimizer (SA ω) (Sb ω) (xHat ω))
    (horig : ∀ x : Fin n → ℝ,
      lsObjective A b x = vecNorm2Sq (coord x))
    (hsketch : ∀ ω x,
      lsObjective (SA ω) (Sb ω) x =
        vecNorm2Sq (coord x) +
          ∑ j : Fin d, coord x j * matMulVec d (E ω) (coord x) j) :
    α ≤ P.eventProb
      {ω | lsObjective A b (xHat ω) ≤
        (1 + η) * lsObjective A b xOpt} := by
  have hpresProb :
      α ≤ P.eventProb
        {ω | PreservesLSObjective A b (SA ω) (Sb ω) ε} :=
    eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error
      P A b SA Sb coord E hprob horig hsketch
  exact
    eventProb_lsObjective_le_one_add_eta_of_preserves
      P A b SA Sb xHat xOpt hε hfactor hpresProb hhat























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
