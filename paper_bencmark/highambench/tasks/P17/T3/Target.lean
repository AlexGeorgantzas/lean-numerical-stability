import HighamBench.P17Definitions

namespace HighamBench

/-- P17-T3: exact finite-probability assembly behind Theorem 4.3. A centered
second-moment radius and the limited-precision deterministic bias radius add,
then the summation condition factor scales the resulting event. -/
theorem p17_t3_variance_plus_bias_probability_bound
    {Ω : Type*} [Fintype Ω] (P : P17FiniteProbability Ω)
    (centered : Ω → ℝ) (bias varianceBudget biasRadius kappa lambda : ℝ)
    (hvariance : 0 < varianceBudget) (hlambda : 0 < lambda)
    (hkappa : 0 ≤ kappa)
    (hmoment : p17Expectation P (fun ω => (centered ω) ^ 2) ≤ varianceBudget)
    (hbias : |bias| ≤ biasRadius) :
    1 - lambda ≤
      p17EventProb P {ω |
        |kappa * (centered ω + bias)| ≤
          kappa * (Real.sqrt (varianceBudget / lambda) + biasRadius)} := by
  -- PROOF_START
  sorry

end HighamBench
