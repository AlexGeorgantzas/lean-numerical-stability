import Mathlib.Data.Real.Basic
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# Basic

Canonical reusable module extracted without change from LSPerturbation.
-/

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

end NumStability
