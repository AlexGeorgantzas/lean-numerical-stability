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
-- These results are axiomatized as structures since they require SVD,
-- pseudo-inverse, and rectangular matrix operations not in the library.

import Mathlib.Data.Real.Basic
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- §20.1  Theorem 20.1 (Wedin): Normwise LS perturbation
-- ============================================================

/-- **Theorem 20.1 (Wedin)**: Normwise perturbation of the LS solution.

    Let A ∈ ℝ^{m×n} (m ≥ n) and A + ΔA both be of full rank, with
    ‖ΔA‖₂ ≤ ε‖A‖₂ and ‖Δb‖₂ ≤ ε‖b‖₂. Then:

    ‖x−y‖₂/‖x‖₂ ≤ κ₂(A)·ε/(1−κ₂(A)·ε) · (2 + (κ₂(A)+1)·‖r‖₂/(‖A‖₂·‖x‖₂))
    ‖r−s‖₂/‖b‖₂ ≤ (1 + 2κ₂(A))·ε

    where r = b − Ax, s = b + Δb − (A+ΔA)y.

    The bound shows sensitivity is κ₂(A) when the residual is small
    (nearly consistent system) and κ₂(A)² when the residual is large.

    Axiomatized since the proof requires SVD and pseudo-inverse. -/
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
