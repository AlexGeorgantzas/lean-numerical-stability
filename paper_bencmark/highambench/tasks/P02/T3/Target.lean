import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

/-- P02-T3: the no-multiplication-underflow `DotK` bound in Proposition 5.11. -/
theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (p02Gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (p02Gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START
  sorry

end HighamBench
