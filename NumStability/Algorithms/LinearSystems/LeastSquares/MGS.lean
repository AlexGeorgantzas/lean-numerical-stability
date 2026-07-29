import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# MGS

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Source-facing exact factorization data for Higham, 2nd ed., Chapter 20,
    Section 20.3:
    `[A b] = [Q₁ q] [[R z], [0 ρ]]`, with `q` orthogonal to the columns of
    `Q₁` and with the displayed columns normalized as produced by exact MGS.

    This is an exact algebraic certificate, not a floating-point MGS
    implementation or stability theorem. -/
structure MGSAugmentedLSFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z : Fin n → ℝ) (rho : ℝ) : Prop where
  /-- Matrix columns satisfy `A = Q₁R`. -/
  A_eq : ∀ i j, A i j = ∑ k : Fin n, Q1 i k * R k j
  /-- Right-hand side column satisfies `b = Q₁z + ρq`. -/
  b_eq : ∀ i, b i = ∑ k : Fin n, Q1 i k * z k + rho * q i
  /-- Columns of `Q₁` are orthonormal. -/
  Q1_col_orthonormal :
    ∀ j k : Fin n, ∑ i : Fin m, Q1 i j * Q1 i k =
      if j = k then 1 else 0
  /-- The final column `q` is orthogonal to every column of `Q₁`. -/
  q_orthogonal : ∀ j : Fin n, ∑ i : Fin m, Q1 i j * q i = 0
  /-- The final column `q` has Euclidean norm one. -/
  q_norm : vecNorm2Sq q = 1
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    from `[A b] = [Q₁ q] [[R z], [0 ρ]]`,
    `A x - b = Q₁(Rx-z) - ρq`. -/
theorem MGSAugmentedLSFactorization.residual_eq {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    (x : Fin n → ℝ) :
    lsResidual A b x = mgsAugmentedResidualExpansion Q1 q R z x rho := by
  ext i
  unfold lsResidual mgsAugmentedResidualExpansion
  rw [mgsAugmented_matVec_eq x h.A_eq i, h.b_eq i]
  unfold rectMatMulVec
  rw [← mgsAugmented_sum_diff Q1 R z x i]
  ring
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    if `[A b] = [Q₁ q] [[R z], [0 ρ]]`, with `q` orthogonal to the columns of
    `Q₁`, then `||A x - b||₂² = ||R x - z||₂² + ρ²`.  The book writes the
    equivalent norm of `b - A x`. -/
theorem MGSAugmentedLSFactorization.objective_eq_top_plus_rho_sq
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    (x : Fin n → ℝ) :
    lsObjective A b x =
      vecNorm2Sq (mgsAugmentedTopResidual R z x) + rho ^ 2 := by
  unfold lsObjective
  rw [h.residual_eq x]
  exact
    vecNorm2Sq_mgsAugmentedResidualExpansion
      Q1 q R z x rho h.Q1_col_orthonormal h.q_orthogonal h.q_norm
/-- Higham, 2nd ed., Chapter 20, Section 20.3:
    the exact augmented-MGS least-squares algebra implies that any solution of
    `R x = z` is an exact least-squares minimizer for the original problem.
    This formalizes the source statement "the LS solution is `x = R^{-1} z`"
    without assuming a concrete inverse for `R`. -/
theorem MGSAugmentedLSFactorization.isLeastSquaresMinimizer_of_solve
    {m n : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {Q1 : Fin m → Fin n → ℝ} {q : Fin m → ℝ}
    {R : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {rho : ℝ}
    (h : MGSAugmentedLSFactorization A b Q1 q R z rho)
    {x : Fin n → ℝ}
    (hsolve : ∀ k : Fin n, matMulVec n R x k = z k) :
    IsLeastSquaresMinimizer A b x := by
  intro y
  rw [h.objective_eq_top_plus_rho_sq x, h.objective_eq_top_plus_rho_sq y]
  have htop_zero : vecNorm2Sq (mgsAugmentedTopResidual R z x) = 0 := by
    unfold vecNorm2Sq mgsAugmentedTopResidual
    apply Finset.sum_eq_zero
    intro k _
    rw [hsolve k]
    ring
  rw [htop_zero]
  have hnonneg : 0 ≤ vecNorm2Sq (mgsAugmentedTopResidual R z y) :=
    vecNorm2Sq_nonneg (mgsAugmentedTopResidual R z y)
  nlinarith

end NumStability
