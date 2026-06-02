-- Algorithms/QR/HouseholderOneStep.lean
--
-- Bridge from concrete Householder construction to concrete Householder
-- application for one reflector.

import LeanFpAnalysis.FP.Algorithms.QR.HouseholderReflector
import LeanFpAnalysis.FP.Algorithms.QR.HouseholderApply

namespace LeanFpAnalysis.FP

open scoped BigOperators Matrix.Norms.Frobenius

/-- Concrete construction plus concrete application satisfies the normalized
    one-reflector application contract.

    This combines the implementation-backed construction theorem
    `fl_householderVectorError` with the implementation-backed application
    theorem `fl_householderApply_normalized_appError`.  The exact reflector is
    written in Higham's normalized form `I - v vᵀ`, where `v` is the normalized
    exact Householder vector produced from the input `x`.

    The raw bound is
    `sqrt(n*u^2) + 2*gamma(11n+23)`, obtained by instantiating the application
    theorem with the construction perturbation index `a = 5n+10`. -/
theorem fl_householderConstructApply_appError (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x b : Fin n → ℝ)
    (hx : x ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23)) :
    HouseholderAppError n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      b
      (fl_householderApply fp n
        (fl_householderNormalizedVector fp hn0 x) 1 b)
      (Real.sqrt ((n : ℝ) * fp.u ^ 2) +
        2 * gamma fp (11 * n + 23)) := by
  let a : ℕ := 5 * n + 10
  let v : Fin n → ℝ :=
    householderNormalizedVector n
      (householderVector hn0 x) (householderBetaFromScale hn0 x)
  let v_hat : Fin n → ℝ := fl_householderNormalizedVector fp hn0 x
  have hvalid_vec : gammaValid fp (8 * n + 16) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalid_eps : gammaValid fp a :=
    gammaValid_mono fp (by omega) hvalid
  have hvec : HouseholderVectorError n v v_hat (gamma fp a) := by
    simpa [v, v_hat, a] using
      fl_householderVectorError fp hn0 x hx hvalid_vec
  have heps_nonneg : 0 ≤ gamma fp a := gamma_nonneg fp hvalid_eps
  have hvalid_apply : gammaValid fp (2 * a + n + 3) := by
    exact gammaValid_mono fp (by unfold a; omega) hvalid
  have happ :=
    fl_householderApply_normalized_appError fp a n v v_hat (gamma fp a) b
      hvec heps_nonneg le_rfl hvalid_apply
  have hidx : 2 * a + n + 3 = 11 * n + 23 := by
    unfold a
    omega
  rw [hidx] at happ
  simpa [v, v_hat] using happ

end LeanFpAnalysis.FP
