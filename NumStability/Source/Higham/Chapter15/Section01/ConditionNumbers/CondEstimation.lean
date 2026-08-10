import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Section01 ConditionNumbers CondEstimation

Canonical destination for material split out of
`NumStability.Algorithms.CondEstimation` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- **Norm identity** (Higham §14.1, eq 14.1).

    For d ≥ 0 and D = diag(d):
      ‖|A⁻¹| d‖∞ = ‖A⁻¹ D‖∞.

    This reduces componentwise condition estimation (which requires |A⁻¹|)
    to a matrix norm estimation problem (which only requires A⁻¹ D).
    The key insight: when d ≥ 0, |A⁻¹_{ij}| · d_j = |A⁻¹_{ij} · d_j|,
    so the row sums coincide. -/
theorem cond_norm_identity (n : ℕ) (_hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) =
    infNorm (fun i j => A_inv i j * d j) := by
  let w : Fin n → ℝ := fun i => ∑ j : Fin n, |A_inv i j| * d j
  let B : Fin n → Fin n → ℝ := fun i j => A_inv i j * d j
  have hrow : ∀ i : Fin n, w i = ∑ j : Fin n, |B i j| := by
    intro i
    unfold w B
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul, abs_of_nonneg (hd j)]
  have hw_nonneg : ∀ i : Fin n, 0 ≤ w i := by
    intro i
    unfold w
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  change infNormVec w = infNorm B
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      rw [abs_of_nonneg (hw_nonneg i), hrow i]
      exact row_sum_le_infNorm B i
    · exact infNorm_nonneg B
  · apply infNorm_le_of_row_sum_le
    · intro i
      rw [← hrow i, ← abs_of_nonneg (hw_nonneg i)]
      exact abs_le_infNormVec w i
    · exact infNormVec_nonneg w

/-- **1-norm/∞-norm duality** (Higham §14.1, equation after 14.1).

    ‖B‖₁ = ‖Bᵀ‖∞: the 1-norm of B equals the ∞-norm of its transpose.
    This connects 1-norm condition estimation to ∞-norm problems. -/
theorem oneNorm_eq_infNorm_transpose' (n : ℕ) (_hn : 0 < n)
    (B : Fin n → Fin n → ℝ) :
    oneNorm B = infNorm (fun i j => B j i) :=
  oneNorm_eq_infNorm_transpose B

end NumStability
