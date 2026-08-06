import HighamBench.P03Definitions

namespace HighamBench

/-- P03-T2: the exact scalar coefficient assembly in Theorem 4.1. -/
theorem p03_t2_normwise_residual_contraction
    (u us gammaR c1 c2 kappa R D Y eRes eSolve eUpdate Rnext : ℝ)
    (_hden : c1 * kappa * us < 1)
    (hid : Rnext ≤ eRes + eSolve + eUpdate)
    (hres : eRes ≤ us * R + (1 + us) * gammaR * D)
    (hsolve : eSolve ≤
      us * ((c1 * kappa + c2) / (1 - c1 * kappa * us)) *
        ((1 + us) * R + (1 + us) * gammaR * D))
    (hupdate : eUpdate ≤ u * Y) :
    Rnext ≤
      us * (1 + (1 + us) * ((c1 * kappa + c2) /
        (1 - c1 * kappa * us))) * R +
      (1 + us * ((c1 * kappa + c2) /
        (1 - c1 * kappa * us))) * (1 + us) * gammaR * D +
      u * Y := by
  -- PROOF_START
  sorry

end HighamBench
