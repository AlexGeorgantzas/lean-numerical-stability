-- Algorithms/LeastSquares/LSPerturbation.lean
--
-- Perturbation theory for the least squares problem (Higham §20.1).
--
-- Theorem 20.1 (Wedin): Normwise perturbation bounds for the LS solution.
--   ‖x−y‖/‖x‖ ≤ κ₂(A)ε/(1−κ₂(A)ε) · (2 + (κ₂(A)+1)‖r‖/(‖A‖‖x‖))
--   ‖r−s‖/‖b‖ ≤ (1+2κ₂(A))ε
--
-- Theorem 20.2: Componentwise perturbation via the augmented system
--   [I A; Aᵀ 0][r; x] = [b; 0].
--
-- The full Wedin theorem still requires the project-local SVD, pseudoinverse,
-- and projector perturbation route.  The scalar source right-hand sides below
-- are proved infrastructure, while the older structures remain only as legacy
-- contract packages.

import Mathlib.Data.Real.Basic
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §20.1  Theorem 20.1 (Wedin): Normwise LS perturbation
-- ============================================================

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    scalar right-hand side of Wedin's relative solution perturbation bound. -/
noncomputable def wedinTheorem20_1SolutionRelativeRHS
    (kappa eps A_norm x_norm r_norm : ℝ) : ℝ :=
  (kappa * eps) / (1 - kappa * eps) *
    (2 + (kappa + 1) * r_norm / (A_norm * x_norm))

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    scalar right-hand side of Wedin's relative residual perturbation bound. -/
def wedinTheorem20_1ResidualRelativeRHS (kappa eps : ℝ) : ℝ :=
  (1 + 2 * kappa) * eps

/-- The small-perturbation condition in Theorem 20.1 makes the denominator in
    equation (20.1) positive. -/
theorem wedinTheorem20_1_denominator_pos {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    0 < 1 - kappa * eps := by
  linarith

/-- The denominator in Wedin's equation (20.1) is nonzero under the printed
    small-perturbation hypothesis. -/
theorem wedinTheorem20_1_denominator_ne_zero {kappa eps : ℝ}
    (hsmall : kappa * eps < 1) :
    1 - kappa * eps ≠ 0 :=
  (wedinTheorem20_1_denominator_pos hsmall).ne'

/-- Under the natural norm-domain assumptions, Wedin's equation (20.1)
    right-hand side is a nonnegative scalar bound. -/
theorem wedinTheorem20_1_solutionRelativeRHS_nonneg {kappa eps A_norm x_norm r_norm : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) (hsmall : kappa * eps < 1)
    (hA : 0 < A_norm) (hx : 0 < x_norm) (hr : 0 ≤ r_norm) :
    0 ≤ wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm r_norm := by
  unfold wedinTheorem20_1SolutionRelativeRHS
  have hnum : 0 ≤ kappa * eps := mul_nonneg hkappa heps
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hfrac : 0 ≤ (kappa * eps) / (1 - kappa * eps) :=
    div_nonneg hnum (le_of_lt hden_pos)
  have hAx_pos : 0 < A_norm * x_norm := mul_pos hA hx
  have hkappa_one_nonneg : 0 ≤ kappa + 1 := by linarith
  have hterm : 0 ≤ (kappa + 1) * r_norm / (A_norm * x_norm) :=
    div_nonneg (mul_nonneg hkappa_one_nonneg hr) (le_of_lt hAx_pos)
  have hparen : 0 ≤ 2 + (kappa + 1) * r_norm / (A_norm * x_norm) := by
    linarith
  exact mul_nonneg hfrac hparen

/-- Under the natural condition-number and roundoff-domain assumptions,
    Wedin's equation (20.2) right-hand side is nonnegative. -/
theorem wedinTheorem20_1_residualRelativeRHS_nonneg {kappa eps : ℝ}
    (hkappa : 0 ≤ kappa) (heps : 0 ≤ eps) :
    0 ≤ wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  unfold wedinTheorem20_1ResidualRelativeRHS
  have hfactor : 0 ≤ 1 + 2 * kappa := by nlinarith
  exact mul_nonneg hfactor heps

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.1) vanishes. -/
@[simp] theorem wedinTheorem20_1_solutionRelativeRHS_zero_eps
    (kappa A_norm x_norm r_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa 0 A_norm x_norm r_norm = 0 := by
  simp [wedinTheorem20_1SolutionRelativeRHS]

/-- With zero data perturbation budget, the scalar RHS of Wedin's equation
    (20.2) vanishes. -/
@[simp] theorem wedinTheorem20_1_residualRelativeRHS_zero_eps (kappa : ℝ) :
    wedinTheorem20_1ResidualRelativeRHS kappa 0 = 0 := by
  simp [wedinTheorem20_1ResidualRelativeRHS]

/-- In the zero-residual case, Wedin's equation (20.1) loses the residual
    amplification term and reduces to the `2 κ ε / (1 - κ ε)` factor. -/
theorem wedinTheorem20_1_solutionRelativeRHS_of_zero_residual
    (kappa eps A_norm x_norm : ℝ) :
    wedinTheorem20_1SolutionRelativeRHS kappa eps A_norm x_norm 0 =
      2 * ((kappa * eps) / (1 - kappa * eps)) := by
  simp [wedinTheorem20_1SolutionRelativeRHS, mul_comm]

/-- **Theorem 20.1 (Wedin)**: Normwise perturbation of the LS solution.

    Let A ∈ ℝ^{m×n} (m ≥ n) and A + ΔA both be of full rank, with
    ‖ΔA‖₂ ≤ ε‖A‖₂ and ‖Δb‖₂ ≤ ε‖b‖₂. Then:

    ‖x−y‖₂/‖x‖₂ ≤ κ₂(A)·ε/(1−κ₂(A)·ε) · (2 + (κ₂(A)+1)·‖r‖₂/(‖A‖₂·‖x‖₂))
    ‖r−s‖₂/‖b‖₂ ≤ (1 + 2κ₂(A))·ε

    where r = b − Ax, s = b + Δb − (A+ΔA)y.

    The bound shows sensitivity is κ₂(A) when the residual is small
    (nearly consistent system) and κ₂(A)² when the residual is large.

    Legacy contract package only: the source-exact Wedin theorem still remains
    open until the SVD, pseudoinverse, and projector perturbation foundations
    are closed. -/
structure WedinPerturbationBound (n : ℕ)
    (x y : Fin n → ℝ) (kappa eps : ℝ)
    (sol_bound res_bound : ℝ) : Prop where
  /-- κ₂(A) > 0. -/
  kappa_pos : 0 < kappa
  /-- The perturbation is small enough: κ₂(A)·ε < 1. -/
  small_pert : kappa * eps < 1
  /-- Solution perturbation bound (eq 20.1):
      ‖x−y‖ ≤ sol_bound where sol_bound depends on κ₂(A), ε, ‖r‖, ‖A‖, ‖x‖. -/
  solution : ∀ i, |y i - x i| ≤ sol_bound
  /-- Residual perturbation bound (eq 20.2):
      ‖r−s‖ ≤ res_bound where res_bound ≤ (1+2κ₂(A))·ε·‖b‖. -/
  residual_bound_val : res_bound ≤ (1 + 2 * kappa) * eps

-- ============================================================
-- §20.1  Theorem 20.2: Componentwise LS perturbation
-- ============================================================

/-- **Augmented system for the LS problem** (Higham eq 20.3).

    The LS solution x and residual r = b − Ax satisfy the
    (m+n)×(m+n) augmented system:

    [I  A ][r]   [b]
    [Aᵀ 0 ][x] = [0]

    This is equivalent to the normal equations AᵀAx = Aᵀb.

    The inverse of the augmented system matrix has blocks
    involving A⁺ and (AᵀA)⁻¹ (eq 19.6), enabling componentwise
    perturbation analysis.

    We capture the componentwise perturbation result (Theorem 20.2)
    in terms of the n×n Gram inverse (AᵀA)⁻¹, which is representable
    in the library's square-matrix framework. -/
structure LSAugmentedPerturbation (n : ℕ)
    (ATA ATA_inv : Fin n → Fin n → ℝ)
    (x y : Fin n → ℝ) (eps : ℝ)
    (bound_vec : Fin n → ℝ) : Prop where
  /-- (AᵀA)⁻¹ is the inverse of the Gram matrix. -/
  gram_inv : IsInverse n ATA ATA_inv
  /-- The perturbation ε is nonneg. -/
  eps_nonneg : 0 ≤ eps
  /-- Componentwise bound on the solution perturbation (eq 19.8):
      |y_i − x_i| ≤ ε · bound_vec_i
      where bound_vec captures the |(AᵀA)⁻¹|-weighted perturbation. -/
  solution_bound : ∀ i, |y i - x i| ≤ eps * bound_vec i

end LeanFpAnalysis.FP
