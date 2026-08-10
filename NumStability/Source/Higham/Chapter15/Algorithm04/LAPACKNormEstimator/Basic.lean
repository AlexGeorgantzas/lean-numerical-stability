import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Analysis.ConditionEstimatorLowerBound
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.ConditionEstimators

/-!
# Chapter15 Algorithm04 LAPACKNormEstimator Basic

Canonical destination for material split out of
`NumStability.Algorithms.Chapter15CondEst` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- The scalar estimate γ returned by the LAPACK norm estimator (Higham §15.3,
    Algorithm 15.4, p. 293), obtained from the repository's
    `lapackNormEstimator`. -/
noncomputable def H15_Algorithm15_4_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  lapackNormEstimator hn A

/-- **Algorithm 15.4 estimate is a lower bound on κ₁** (Higham §15.3 + §15.1,
    eq. (15.1)).

    Running the LAPACK 1-norm estimator on `B` and scaling by `‖A‖₁` never
    exceeds `‖A‖₁·‖B‖₁ = κ₁(A)` (when `B = A⁻¹`).  Re-export of
    `condOneNumber_ge_scaled_estimator` under a Chapter-15 label. -/
theorem H15_Algorithm15_4_scaled_le_kappaOne {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A * H15_Algorithm15_4_gamma hn B ≤ H15_kappaOne A B :=
  condOneNumber_ge_scaled_estimator hn A B

/-- **LAPACK estimate under-estimates the textbook κ₁(A)** (Higham §15.3 +
    §15.1, eq. (15.1)) — the headline Chapter-15 condition-estimation result.

    For invertible `A` with supplied inverse `B` (`A * B = 1`), the scaled
    LAPACK 1-norm estimate is a genuine lower bound on `‖A‖₁·‖A⁻¹‖₁`.
    Re-export of `lapack_condEstimate_le_kappaOne`. -/
theorem H15_Algorithm15_4_condEstimate_le_kappaOne {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    oneNorm A * H15_Algorithm15_4_gamma hn B ≤
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) :=
  lapack_condEstimate_le_kappaOne hn A B h

end Higham15
end NumStability
