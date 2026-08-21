import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T3: Theorem 6.3 for one fixed-precision, fully stored restarted
MGS-GMRES execution. The per-restart contractions have the paper's common
`Lambda`, and their iteration gives a geometric envelope down to the two
high-precision floors, modulo uniform second-order terms. -/
theorem p16_t3_mixed_precision_geometric_convergence
    {n : ℕ} (run : P16FixedMixedPrecisionGMRESRun n)
    (hLambda :
      0 ≤ p16FixedMixedContraction run ∧
        p16FixedMixedContraction run < 1) :
    ∃ backwardRemainder forwardRemainder : ℕ → ℝ,
      backwardRemainder =
          (fun i ↦ (run.restart i).theorem41.backwardRemainder) ∧
      forwardRemainder =
          (fun i ↦ (run.restart i).theorem41.forwardRemainder) ∧
      p16UniformSecondOrder run.uHigh run.uLow backwardRemainder ∧
      p16UniformSecondOrder run.uHigh run.uLow forwardRemainder ∧
      (∀ i : ℕ,
        p16BackwardError run.A run.b (run.xHat (i + 1)) ≤
          p16FixedMixedContraction run *
              p16BackwardError run.A run.b (run.xHat i) +
            p16FixedBackwardFloor run + |backwardRemainder i|) ∧
      (∀ i : ℕ,
        p16ForwardError run.xExact (run.xHat (i + 1)) ≤
          p16FixedMixedContraction run *
              p16ForwardError run.xExact (run.xHat i) +
            p16FixedForwardFloor run + |forwardRemainder i|) ∧
      p16FixedGeometricEnvelope
        (p16FixedMixedContraction run) (p16FixedBackwardFloor run)
        run.uHigh run.uLow backwardRemainder
        (fun i ↦ p16BackwardError run.A run.b (run.xHat i)) ∧
      p16FixedGeometricEnvelope
        (p16FixedMixedContraction run) (p16FixedForwardFloor run)
        run.uHigh run.uLow forwardRemainder
        (fun i ↦ p16ForwardError run.xExact (run.xHat i)) := by
  -- PROOF_START
  sorry

end HighamBench
