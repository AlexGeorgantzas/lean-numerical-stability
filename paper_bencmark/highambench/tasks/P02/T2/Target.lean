import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

/-- P02-T2: the doubled-working-precision bound for Algorithm 4.4 (`Sum2`). -/
theorem p02_t2_sum2_error_bound
    (fp : ErrorFreeAddModel) (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hvalid : P02GammaValid fp.u (n + 1)) :
    |sum2 fp v - ∑ i : Fin (n + 1), v i| ≤
      fp.u * |∑ i : Fin (n + 1), v i| +
        (p02Gamma fp.u n) ^ 2 * ∑ i : Fin (n + 1), |v i| := by
  -- PROOF_START
  sorry

end HighamBench
