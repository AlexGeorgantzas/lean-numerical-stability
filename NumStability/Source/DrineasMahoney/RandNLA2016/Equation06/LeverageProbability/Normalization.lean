import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.LeverageScore.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.RowNorm.Core

/-!
# NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization

W11 canonical source correspondence destination. Whole commands are copied unchanged from `NumStability.Algorithms.RandNLA.RowSamplingLeverage`; the historical path re-exports this module.
-/

-- Algorithms/RandNLA/RowSamplingLeverage.lean
--
-- Leverage-score row-sampling consequences for Algorithm 2 of
-- Drineas--Mahoney's CACM RandNLA survey.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602









namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2 with leverage-score probabilities

Equation (6) in Drineas--Mahoney defines the row-sampling probabilities by
applying the norm-squared row distribution to an orthonormal-column matrix
`U` spanning the column space of `A`:

`p_i = ||U_i*||_2^2 / ∑_r ||U_r*||_2^2 = ||U_i*||_2^2 / n`.

This file keeps Algorithm 2's sampled sketch and Gram-matrix machinery from
`RowSampling.lean` and `RowSamplingGram.lean`, specializing it to such `U`.
The equation (7) result is stated in vector-action form,
`||Mx||₂ ≤ c ||x||₂` for all `x`, which is the operator-2-norm inequality
without introducing a separate supremum-valued spectral norm.
-/

-- ============================================================
-- Leverage-score probabilities: equation (6)
-- ============================================================




























































































































































































/-- Equation (6) in denominator-`n` form:
    `p_i = ||U_i*||₂² / n`. -/
theorem leverageScoreProb_eq_rowNormSq_div_nat {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (i : Fin m) :
    leverageScoreProb U i = leverageScore U i / (n : ℝ) := by
  unfold leverageScoreProb leverageScore rowSqNormProb
  rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]

















-- ============================================================
-- One-step rank-one facts for source-sharp equation (7) concentration
-- ============================================================















































































-- ============================================================
-- Equation (7): exact arithmetic
-- ============================================================






























































-- ============================================================
-- Floating-point leverage-score stability and equation (7)
-- ============================================================




























































































































end NumStability
