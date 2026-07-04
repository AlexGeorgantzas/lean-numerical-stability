-- Algorithms/QR/Higham19Labels.lean
--
-- Higham Chapter 19 "QR Factorization" (2nd ed.): source-faithful labeled
-- wrappers packaging already-proved QR mathematics under the printed
-- Lemma/Theorem numbers, following the completed Chapter 19 source-inventory
-- audit.  Each wrapper is honest about the exact constant it proves versus
-- the printed gamma-tilde class, and about which constructions are covered.

import LeanFpAnalysis.FP.Algorithms.QR.HouseholderReflector
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderSpec
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderApply
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderOneStep
import LeanFpAnalysis.FP.Analysis.Rounding

namespace LeanFpAnalysis.FP

open scoped BigOperators

-- ============================================================
-- Lemma 19.1 (Householder vector construction), Construction 1
-- ============================================================

/-- **Lemma 19.1, Construction 1** (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §19.3, p. 357): for the usual-sign
    Householder construction (eq (19.1)), the computed Householder data
    satisfy the exact-tail / relative-error-first-entry / relative-error-beta
    contract `HouseholderConstructionError`.

    Scope: the printed Lemma 19.1 states the bound for BOTH sign
    conventions (19.1) and (19.2); this wrapper covers Construction 1 only.
    The alternative-sign kernel (19.2), with its cancellation-avoiding
    first-entry formula, is not yet formalized, so the full two-construction
    label remains partial.  The proved constant is the `θ̃`/`γ̃_n`-class
    bound recorded in `HouseholderConstructionError` (explicit index
    `4n+8`). -/
theorem H19_Lemma19_1_construction1_backward_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (4 * n + 8)) :
    HouseholderConstructionError fp hn0 x
      (fl_householderVector fp hn0 x)
      (fl_householderBeta fp hn0 x) :=
  fl_householderConstructionError fp hn0 x hx hn

-- ============================================================
-- Lemma 19.2 (backward error of applying a Householder reflector)
-- ============================================================

/-- Constants-collapse for Lemma 19.2: the two-term computed bound
    `√(n·u²) + 2·γ_{11n+23}` is dominated by the single `γ`-class constant
    `γ_{23n+46}`, under the smallness guard `gammaValid fp (23n+46)`.

    Proof: `√(n·u²) = √n·u ≤ n·u ≤ γ_n`; `2·γ_{11n+23} ≤ γ_{22n+46}` and
    `γ_n + γ_{22n+46} ≤ γ_{23n+46}` by two applications of `gamma_sum_le`. -/
theorem sqrt_u_sq_add_two_gamma_le_gamma (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (hval : gammaValid fp (23 * n + 46)) :
    Real.sqrt ((n : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * n + 23) ≤
      gamma fp (23 * n + 46) := by
  have hu : (0 : ℝ) ≤ fp.u := fp.u_nonneg
  -- √(n·u²) = √n · u
  have hsqrt : Real.sqrt ((n : ℝ) * fp.u ^ 2) = Real.sqrt (n : ℝ) * fp.u := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
  -- √n ≤ n
  have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [(by exact_mod_cast hn : (1:ℝ) ≤ (n:ℝ))])
    rwa [Real.sqrt_sq (by positivity)] at this
  -- n·u ≤ γ_n
  have hval_n : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hnu_le : (n : ℝ) * fp.u ≤ gamma fp n := by
    unfold gamma
    have hd : (0 : ℝ) < 1 - (n : ℝ) * fp.u := by
      have := hval_n; unfold gammaValid at this; linarith
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)) hu)
      (mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)) hu)]
  have hsqrt_le : Real.sqrt ((n : ℝ) * fp.u ^ 2) ≤ gamma fp n := by
    rw [hsqrt]
    calc Real.sqrt (n : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right hsqn hu
      _ ≤ gamma fp n := hnu_le
  have hval_11 : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (by omega) hval
  have hval_22 : gammaValid fp (22 * n + 46) :=
    gammaValid_mono fp (by omega) hval
  -- 2·γ_{11n+23} ≤ γ_{22n+46}
  have h2g : 2 * gamma fp (11 * n + 23) ≤ gamma fp (22 * n + 46) := by
    have hsum := gamma_sum_le fp (11 * n + 23) (11 * n + 23)
      (by rw [show (11*n+23)+(11*n+23) = 22*n+46 by ring]; exact hval_22)
    rw [show (11*n+23)+(11*n+23) = 22*n+46 by ring] at hsum
    have hnn : 0 ≤ gamma fp (11 * n + 23) * gamma fp (11 * n + 23) :=
      mul_nonneg (gamma_nonneg fp hval_11) (gamma_nonneg fp hval_11)
    nlinarith [hsum]
  -- γ_n + γ_{22n+46} ≤ γ_{23n+46}
  have hsum2 := gamma_sum_le fp n (22 * n + 46)
    (by rw [show n + (22*n+46) = 23*n+46 by ring]; exact hval)
  rw [show n + (22*n+46) = 23*n+46 by ring] at hsum2
  have hnn2 : 0 ≤ gamma fp n * gamma fp (22 * n + 46) :=
    mul_nonneg (gamma_nonneg fp hval_n) (gamma_nonneg fp hval_22)
  calc Real.sqrt ((n : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * n + 23)
      ≤ gamma fp n + gamma fp (22 * n + 46) := by gcongr
    _ ≤ gamma fp (23 * n + 46) := by nlinarith [hsum2, hnn2]

/-- **Lemma 19.2** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.3, p. 358): applying a computed normalized Householder
    reflector `v̂` (satisfying the normalized construction of `HouseholderApply`)
    to a vector `b` gives `ŷ = (P + ΔP)b` with `P = I − vvᵀ` orthogonal and
    `‖ΔP‖_F` bounded by the single `γ`-class constant `γ_{33n+69}`.

    This packages `fl_householderConstructApply_appError` with the
    constants-collapse `sqrt_u_sq_add_two_gamma_le_gamma`, matching the
    printed backward-error shape (the printed constant is `γ̃_m`; the proved
    constant `γ_{23n+46}` is of the same class with an explicit larger
    index). -/
theorem H19_Lemma19_2_householder_apply_backward_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x b : Fin n → ℝ) (hx : x ≠ 0)
    (hvalid : gammaValid fp (23 * n + 46)) :
    HouseholderAppError n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      b
      (fl_householderApply fp n
        (fl_householderNormalizedVector fp hn0 x) 1 b)
      (gamma fp (23 * n + 46)) := by
  have hbase := fl_householderConstructApply_appError fp hn0 x b hx
    (gammaValid_mono fp (by omega) hvalid)
  obtain ⟨horth, ΔP, hΔ, heq⟩ := hbase
  refine ⟨horth, ΔP, ?_, heq⟩
  exact hΔ.trans (sqrt_u_sq_add_two_gamma_le_gamma fp n hn0 hvalid)

end LeanFpAnalysis.FP
