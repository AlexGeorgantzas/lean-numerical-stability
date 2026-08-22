import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T2: Ramos's fictional-input backward-error interpretation on printed
page 768. The operational FFT family varies over positive `epsilon` tending to
zero, `T` is the positive-sign unnormalized complex DFT, and the imported
stage-local analysis of equations `(3.6)`--`(3.8)` establishes the preceding
Theorem 1(a) bound. A single epsilon-independent coefficient witnesses both
displayed `O(epsilon^2)` terms throughout a right neighborhood of zero. -/
theorem p09_t2_fictional_input_backward_error
    {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (input : ZMod n → ℂ)
    (stageBounds : P09TheoremOneStageEnvelope plan γ input)
    (family : P09AsymptoticFftFamily plan γ)
    (family_input : family.input = input) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∃ δ : P09PositiveEpsilon → ZMod n → ℂ,
          (∀ ε,
            p09FamilyFftRoundoffError family ε = p09FourierTransform (δ ε) ∧
            p09ComplexRms (δ ε) =
              p09ComplexRms (p09FamilyFftRoundoffError family ε) /
                Real.sqrt (n : ℝ)) ∧
          ∀ ε, ε.1 ≤ radius →
            p09ComplexRms (δ ε) ≤
                ε.1 * p09K plan γ * p09ComplexRms input +
                  (secondOrderCoeff * ε.1 ^ 2) /
                    Real.sqrt (n : ℝ) ∧
              p09ComplexMax (δ ε) ≤
                ε.1 * Real.sqrt (n : ℝ) * p09K plan γ *
                    p09ComplexRms input +
                  secondOrderCoeff * ε.1 ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
