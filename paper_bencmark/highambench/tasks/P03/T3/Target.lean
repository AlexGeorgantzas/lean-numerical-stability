import HighamBench.P03Definitions

namespace HighamBench

/-- P03-T3: componentwise residual recurrence in Theorem 5.1. -/
theorem p03_t3_componentwise_residual_recurrence
    {n : ℕ} (us u gammaR : ℝ)
    (M1 P : Fin n → Fin n → ℝ)
    (oldResidual data update correction newResidual : Fin n → ℝ)
    (hresolvent : P03ResolventInverse M1 P)
    (hcorrection : ∀ i : Fin n,
      correction i ≤ p03MatVec P correction i +
        ((1 + us) * |oldResidual i| +
          (1 + us) * (1 + u) * gammaR * data i))
    (hbase : ∀ i : Fin n,
      |newResidual i| ≤
        us * |oldResidual i| +
          (1 + us) * (1 + u) * gammaR * data i +
          correction i + u * update i) :
    ∀ i : Fin n,
      |newResidual i| ≤
        us * |oldResidual i| +
          (1 + us) * p03MatVec M1 (p03VecAbs oldResidual) i +
          (1 + us) * (1 + u) * gammaR *
            (data i + p03MatVec M1 data i) +
          u * update i := by
  -- PROOF_START
  sorry

end HighamBench
