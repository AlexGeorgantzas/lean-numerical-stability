import HighamBench.P06Definitions

namespace HighamBench

/-- P06-T1: Theorem 4.4, equations (4.16)--(4.17), and its Frobenius
consequence (4.20). Apply the preceding one-column result to every input
column, intersect the events, assemble one matrix perturbation, and aggregate
the simultaneous column bounds without changing the computed factor. -/
theorem p06_t1_householder_qr_frobenius_backward_error
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (model : P06Model15 Ω)
    (run : P06HouseholderQRRun Ω m n A model)
    (c5 c6 : ℕ) (lambda : ℝ)
    (_hc5 : 0 < c5) (_hc6 : 0 < c6) (hlambda : 0 < lambda)
    (hlocal : P06Lemma42Assumption run c5 lambda)
    (perColumn : ∀ j,
      P06Lemma42ColumnCertificate run c5 c6 lambda hlocal j) :
    ∃ (goodEvent : Set Ω) (Q : Ω → Fin m → Fin m → ℝ)
        (DeltaA : Ω → Fin m → Fin n → ℝ)
        (columnRemainder : Fin n → ℝ → Ω → ℝ)
        (normwiseRemainder : ℝ → Ω → ℝ),
      MeasurableSet goodEvent ∧
      (∀ j omega,
        P06SecondOrderControl (fun u ↦ columnRemainder j u omega)
          model.unitRoundoff) ∧
      (∀ omega, P06SecondOrderControl
        (fun u ↦ normwiseRemainder u omega) model.unitRoundoff) ∧
      p06P4 lambda m n ≤
        model.probability.real goodEvent ∧
      (∀ omega,
        p06UpperTrapezoidal (run.RHat omega) ∧
        p06Orthogonal (Q omega) ∧
        A + DeltaA omega = p06RectMatMul (Q omega) (run.RHat omega)) ∧
      ∀ omega, omega ∈ goodEvent →
        (∀ j,
          p06VecNorm2 (fun i ↦ DeltaA omega i j) ≤
            p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
                p06VecNorm2 (fun i ↦ A i j) +
              |columnRemainder j model.unitRoundoff omega|) ∧
          p06FrobNorm (DeltaA omega) ≤
          p06QRLeadingCoefficient c6 lambda m n model.unitRoundoff *
              p06FrobNorm A +
            normwiseRemainder model.unitRoundoff omega := by
  -- PROOF_START
  sorry

end HighamBench
