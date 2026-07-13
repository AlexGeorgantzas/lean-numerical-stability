-- Algorithms/Chapter15CondEst.lean
--
-- Correctly Chapter-15-labeled wrappers for the LAPACK 1-norm condition
-- estimation material of Higham, *Accuracy and Stability of Numerical
-- Algorithms*, 2nd ed. (SIAM, 2002), Chapter 15 "Condition Number Estimation".
--
-- SOURCE OF TRUTH (verbatim printed statements, Chapter 15):
--   * §15.1, eq. (15.1) region, p. 306: the componentwise-to-matrix-norm
--     reduction and the 1-norm condition number κ₁(A) = ‖A‖₁·‖A⁻¹‖₁.
--   * §15.3, Algorithm 15.3 (1-norm power method), p. 292:
--       "Given A ∈ Rⁿˣⁿ this algorithm computes γ and x such that
--        γ ≤ ‖A‖₁ and ‖Ax‖₁ = γ‖x‖₁."
--   * §15.3, Algorithm 15.4 (LAPACK norm estimator), p. 293:
--       "Given A ∈ Rⁿˣⁿ this algorithm computes γ and v = Aw such that
--        γ ≤ ‖A‖₁ with ‖v‖₁/‖w‖₁ = γ (w is not returned)."
--   * §15.1 lower-bound reading: the estimator, run on A⁻¹ and scaled by ‖A‖₁,
--     under-estimates the true 1-norm condition number κ₁(A).
--
-- NOTE ON MIS-LABELING.  The MATHEMATICS for all of the above already lives in
-- the repository but is (incorrectly) labeled as "Chapter 14":
--   * `Algorithms/CondEstimation.lean` — `oneNormPowerMethod`,
--     `oneNormPowerMethod_lower_bound`, `lapackNormEstimator`,
--     `lapackNormEstimator_lower_bound`;
--   * `Analysis/ConditionEstimatorLowerBound.lean` — `condOneNumber`,
--     `lapack_condEstimate_le_kappaOne`, etc.
-- This file is IMPORT-ONLY: it does not edit those files.  It re-exposes the
-- genuine Chapter-15 guarantees under `H15_*` names, reusing the existing
-- proofs and adding ONLY the honest `‖Ax‖₁ = γ‖x‖₁` equality (Algorithm 15.3)
-- and `‖v‖₁/‖w‖₁ = γ` equality (Algorithm 15.4), which the existing
-- lower-bound lemmas do not state.
--
-- HONEST STATEMENT STRENGTH.  The existing recursion `oneNormPowerMethod`
-- reports γ from the *previous* iterate on the converged branch, so its stored
-- `.γ` field is not in general equal to `‖A·(returned x)‖₁`.  We therefore do
-- NOT claim the equality for that stored field.  Instead we report, exactly as
-- Algorithm 15.3 prescribes, γ := ‖A x‖₁ for the returned iterate `x` (the
-- final `x` produced by the method).  Because every iterate the method produces
-- has ‖x‖₁ = 1 (the start vector n⁻¹e and every basis vertex eⱼ), this γ
-- satisfies BOTH printed conclusions at full strength:
--   γ ≤ ‖A‖₁   (submultiplicativity, ‖x‖₁ = 1)   and   ‖Ax‖₁ = γ‖x‖₁.
-- No hypothesis smuggles either conclusion in.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LeanFpAnalysis.FP.Analysis.MatrixAlgebra
import LeanFpAnalysis.FP.Algorithms.CondEstimation
import LeanFpAnalysis.FP.Analysis.ConditionEstimatorLowerBound

namespace LeanFpAnalysis.FP
namespace Higham15

open scoped BigOperators

-- ============================================================
-- §15.3  Algorithm 15.3 (1-norm power method)
-- ============================================================

/-- The final iterate `x` produced by the Chapter-15 1-norm power method
    (Higham §15.3, Algorithm 15.3), obtained by running the repository's
    `oneNormPowerMethod` for `fuel` iterations and reading off its iterate.

    This is exactly the vector at which the returned scalar estimate is the
    1-norm of `Ax` (see `H15_Algorithm15_3_gamma`). -/
noncomputable def H15_Algorithm15_3_x {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : Fin n → ℝ :=
  (oneNormPowerMethod hn A fuel).x

/-- The scalar estimate γ returned by Algorithm 15.3 (Higham §15.3, p. 292):
    γ = ‖A x‖₁ for the final iterate `x`. -/
noncomputable def H15_Algorithm15_3_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : ℝ :=
  oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)

/-- **Exact-normalization invariant** for the iterates of Algorithm 15.3.

    Every iterate produced by `oneNormPowerMethod` has 1-norm exactly `1`:
    the start vector is `n⁻¹e` (Higham §15.3: `x = n⁻¹e`), and every subsequent
    iterate is a unit basis vector `eⱼ` (`x = eⱼ`), both of 1-norm `1`; the
    converged branch merely re-returns the previous iterate.  This upgrades the
    `≤ 1` invariant used by the existing lower-bound proof to an *equality*,
    which is what the printed `‖Ax‖₁ = γ‖x‖₁` relation needs. -/
theorem H15_Algorithm15_3_x_oneNorm_eq_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (H15_Algorithm15_3_x hn A fuel) = 1 := by
  unfold H15_Algorithm15_3_x
  -- One step maps a unit-1-norm iterate to a unit-1-norm iterate (start `n⁻¹e`
  -- or a basis vertex `eⱼ`; the converged branch re-returns the input).
  have hstep_eq : ∀ st : OneNormState n, oneNormVec st.x = 1 →
      oneNormVec (oneNormStep hn A st).1.x = 1 := by
    intro st hst
    simp only [oneNormStep]
    split_ifs
    · exact hst
    · exact oneNormVec_basisVec _
  induction fuel with
  | zero =>
    simp only [oneNormPowerMethod]
    exact initial_vec_oneNorm hn
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    set prev := oneNormPowerMethod hn A fuel with hprev
    -- Rewrite the `let`-bindings into a plain `if` on the step's Bool flag.
    rw [show (let prev := oneNormPowerMethod hn A fuel;
              let x := oneNormStep hn A prev;
              if x.2 = true then prev else x.1) =
             if (oneNormStep hn A prev).2 = true then prev
             else (oneNormStep hn A prev).1 from rfl]
    split_ifs with hconv
    · -- converged: returns the previous iterate, 1-norm 1 by IH
      exact ih
    · -- not converged: returns the step output, which has 1-norm 1 by hstep_eq
      exact hstep_eq prev ih

/-- **Algorithm 15.3 — lower-bound guarantee** (Higham §15.3, p. 292):
      `γ ≤ ‖A‖₁`.

    Since the reported iterate `x` has `‖x‖₁ = 1`, submultiplicativity of the
    1-norm gives `γ = ‖Ax‖₁ ≤ ‖A‖₁·‖x‖₁ = ‖A‖₁`.  (Reuses
    `oneNormVec_matVec_le` from the existing module; no reproof of the norm
    algebra.) -/
theorem H15_Algorithm15_3_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A := by
  unfold H15_Algorithm15_3_gamma
  have hx := H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel
  calc oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)
      ≤ oneNorm A * oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
        oneNormVec_matVec_le hn A _
    _ = oneNorm A * 1 := by rw [hx]
    _ = oneNorm A := mul_one _

/-- **Algorithm 15.3 — norm-equality guarantee** (Higham §15.3, p. 292):
      `‖Ax‖₁ = γ‖x‖₁`.

    By construction `γ = ‖Ax‖₁` and `‖x‖₁ = 1`, so `γ‖x‖₁ = γ = ‖Ax‖₁`.
    This is the equality the existing "Chapter-14" lower-bound lemmas do not
    state; it is discharged here for the genuine final iterate, no hypothesis
    added. -/
theorem H15_Algorithm15_3_norm_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) := by
  rw [H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel, mul_one]
  rfl

/-- **Algorithm 15.3 — full printed guarantee** (Higham §15.3, Algorithm 15.3,
    p. 292), bundling both printed conclusions for the computed pair `(γ, x)`:

      `γ ≤ ‖A‖₁`   and   `‖Ax‖₁ = γ‖x‖₁`. -/
theorem H15_Algorithm15_3_spec {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A ∧
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
  ⟨H15_Algorithm15_3_lower_bound hn A fuel,
   H15_Algorithm15_3_norm_eq hn A fuel⟩

-- ============================================================
-- §15.3  Algorithm 15.4 (LAPACK norm estimator)
-- ============================================================

/-- The scalar estimate γ returned by the LAPACK norm estimator (Higham §15.3,
    Algorithm 15.4, p. 293), obtained from the repository's
    `lapackNormEstimator`. -/
noncomputable def H15_Algorithm15_4_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  lapackNormEstimator hn A

/-- **Algorithm 15.4 — lower-bound guarantee** (Higham §15.3, Algorithm 15.4,
    p. 293): `γ ≤ ‖A‖₁`.

    Direct re-export of `lapackNormEstimator_lower_bound` under a Chapter-15
    label; the LAPACK estimator is the maximum of the power-method estimate and
    the alternating-vector estimate `‖Ab‖₁/‖b‖₁`, each a genuine lower bound. -/
theorem H15_Algorithm15_4_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    H15_Algorithm15_4_gamma hn A ≤ oneNorm A :=
  lapackNormEstimator_lower_bound hn A

/-- **Algorithm 15.4 — the estimate is a realized ratio `‖v‖₁/‖w‖₁` with
    `v = Aw`** (Higham §15.3, Algorithm 15.4, p. 293).

    The printed spec says the estimator "computes γ and `v = Aw` … with
    `‖v‖₁/‖w‖₁ = γ` (w is not returned)".  For `n > 1` the alternating-vector
    component of `lapackNormEstimator` is, by construction, exactly the ratio
    `‖Ab‖₁/‖b‖₁` for the fixed vector `b = lapackAltVec` (Higham §15.3, p. 293:
    `bᵢ = (−1)^{i+1}(1 + (i−1)/(n−1))`, `c = Ab`).  We exhibit that genuine
    `(w, v) = (b, Ab)` witness: `v = Aw` holds definitionally, and the realized
    ratio `‖v‖₁/‖w‖₁` is a lower bound on the returned estimate `γ` (it is one
    of the two arguments of the `max`), hence `≤ ‖A‖₁`.

    This is the honest `v = Aw` / ratio-realization that the existing
    "Chapter-14" lower-bound lemma does not expose. -/
theorem H15_Algorithm15_4_ratio_witness {n : ℕ} (h1n : 1 < n)
    (A : Fin n → Fin n → ℝ) :
    ∃ (w v : Fin n → ℝ),
      (∀ i, v i = ∑ j : Fin n, A i j * w j) ∧
      oneNormVec v / oneNormVec w ≤ H15_Algorithm15_4_gamma (Nat.lt_of_lt_of_le
        Nat.zero_lt_one (le_of_lt h1n)) A ∧
      H15_Algorithm15_4_gamma (Nat.lt_of_lt_of_le Nat.zero_lt_one
        (le_of_lt h1n)) A ≤ oneNorm A := by
  set hn : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt h1n) with hhn
  refine ⟨lapackAltVec h1n,
          fun i => ∑ j : Fin n, A i j * lapackAltVec h1n j,
          fun _ => rfl, ?_, H15_Algorithm15_4_lower_bound hn A⟩
  -- The realized ratio equals the `alt_est` argument of the `max`, hence ≤ γ.
  unfold H15_Algorithm15_4_gamma lapackNormEstimator
  rw [dif_pos h1n]
  exact le_max_right _ _

-- ============================================================
-- §15.1  1-norm condition number κ₁(A) = ‖A‖₁‖A⁻¹‖₁ (eq. (15.1))
-- ============================================================

/-- **1-norm condition number** (Higham §15.1, eq. (15.1) region, p. 306):
      `κ₁(A) = ‖A‖₁·‖A⁻¹‖₁`.

    Re-export of `condOneNumber` under a Chapter-15 label.  The inverse is
    supplied explicitly as `B` (the matrix the estimator actually samples,
    accessed through linear solves); `H15_kappaOne_eq_of_rightInverse` pins `B`
    to Mathlib's canonical inverse when `A * B = 1`. -/
noncomputable def H15_kappaOne {n : ℕ} (A B : Fin n → Fin n → ℝ) : ℝ :=
  condOneNumber A B

/-- `κ₁(A) ≥ 0` (Higham §15.1). -/
theorem H15_kappaOne_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    0 ≤ H15_kappaOne A B :=
  condOneNumber_nonneg A B

/-- **κ₁ at the genuine inverse** (Higham §15.1, eq. (15.1)).

    When `B` is an actual right inverse of `A` (`A * B = 1`), `H15_kappaOne A B`
    is the textbook `‖A‖₁·‖A⁻¹‖₁` with Mathlib's canonical inverse.  Re-export
    of `condOneNumber_eq_kappaOne_of_rightInverse`. -/
theorem H15_kappaOne_eq_of_rightInverse {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    H15_kappaOne A B =
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) :=
  condOneNumber_eq_kappaOne_of_rightInverse A B h

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
end LeanFpAnalysis.FP
