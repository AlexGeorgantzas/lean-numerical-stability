import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T2: Ramos's fictional-input backward-error interpretation on printed
page 768. The error is produced by the linked mixed-radix FFT run, `T` is the
positive-sign unnormalized complex DFT, and both displayed finite-remainder
bounds retain their exact first-order coefficients. -/
theorem p09_t2_fictional_input_backward_error
    {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (model : P09WilkinsonModel)
    (run : P09MixedRadixFftRun plan model)
    (forward : P09TheoremOneRmsCertificate run) :
    ∃ δ : ZMod n → ℂ,
      p09FftRoundoffError run = p09FourierTransform δ ∧
      p09ComplexRms δ =
        p09ComplexRms (p09FftRoundoffError run) / Real.sqrt (n : ℝ) ∧
      p09ComplexRms δ ≤
        model.epsilon * p09K plan model.gamma * p09ComplexRms run.input +
          (forward.secondOrderCoeff * model.epsilon ^ 2) /
            Real.sqrt (n : ℝ) ∧
      p09ComplexMax δ ≤
        model.epsilon * Real.sqrt (n : ℝ) * p09K plan model.gamma *
            p09ComplexRms run.input +
          forward.secondOrderCoeff * model.epsilon ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
