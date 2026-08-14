import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T1: Theorem 4.4 and its Frobenius consequence (4.20). From the
simultaneous columnwise backward-error certificate, aggregate on the same
event without changing its probability, computed factor, or exact QR
relation. -/
theorem p06_t1_householder_qr_frobenius_backward_error
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (model : P06Model15 Ω)
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 c6 : ℕ) (lambda : ℝ)
    (_hc5 : 0 < c5) (_hc6 : 0 < c6) (hlambda : 0 < lambda)
    (hlocal : P06Lemma42Assumption run c5 lambda)
    (columnwise :
      P06Theorem44ColumnwiseCertificate run c5 c6 lambda hlocal) :
    ∃ (goodEvent : Set Ω) (Q : Ω → Fin m → Fin m → ℝ)
        (DeltaA : Ω → Fin m → Fin n → ℝ)
        (normwiseRemainder : ℝ → Ω → ℝ),
      MeasurableSet goodEvent ∧
      (∀ omega,
        p06SecondOrderAtZero (fun u ↦ normwiseRemainder u omega)) ∧
      p06P4 lambda m n ≤
        ENNReal.toReal (model.probability goodEvent) ∧
      ∀ omega, omega ∈ goodEvent →
        p06UpperTrapezoidal (run.RHat omega) ∧
        p06Orthogonal (Q omega) ∧
        A + DeltaA omega = p06RectMatMul (Q omega) (run.RHat omega) ∧
        p06FrobNorm (DeltaA omega) ≤
          p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
              p06FrobNorm A +
            normwiseRemainder model.unitRoundoff omega := by
  -- PROOF_START
  sorry

end HighamBench
