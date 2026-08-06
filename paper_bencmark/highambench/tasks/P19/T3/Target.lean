import HighamBench.P19Definitions

namespace HighamBench

/-- P19-T3: exact comparison of the right- and flexible-preconditioned
attainable-error envelopes in (3.17) and (3.20), including the term removed by
storing the flexible basis explicitly. -/
theorem p19_t3_right_flexible_envelope_comparison {n : ℕ}
    (ug um ua etaR rhoA : ℝ)
    (AMRinv AMRinvInv MR MRinv A Ainv : Fin n → Fin n → ℝ)
    (hum : 0 ≤ um) (hetaR : 0 ≤ etaR) :
    p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv ≤
        p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv ∧
      p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv =
        p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv +
          um * etaR * p19Kappa2 MR MRinv ∧
      (p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv =
          p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv ↔
        um = 0 ∨ etaR = 0 ∨ p19Kappa2 MR MRinv = 0) ∧
      (0 < um → 0 < etaR → 0 < p19Kappa2 MR MRinv →
        p19FlexibleEnvelope ug ua rhoA AMRinv AMRinvInv MR MRinv A Ainv <
          p19RightEnvelope ug um ua etaR rhoA AMRinv AMRinvInv MR MRinv A Ainv) := by
  -- PROOF_START
  sorry

end HighamBench
