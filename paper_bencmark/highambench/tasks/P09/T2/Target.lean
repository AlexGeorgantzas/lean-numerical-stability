import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T2: Ramos's fictional-input backward-error interpretation on printed
page 768. The operational FFT family varies over positive `epsilon` tending to
zero, `T` is the positive-sign unnormalized complex DFT, and a single
epsilon-independent coefficient witnesses each displayed `O(epsilon^2)` term
throughout a right neighborhood of zero. -/
theorem p09_t2_fictional_input_backward_error
    {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (family : P09AsymptoticFftFamily plan γ)
    (forward : P09TheoremOneRmsAsymptotic family) :
    ∃ δ : P09PositiveEpsilon → ZMod n → ℂ,
      (∀ ε,
        p09FamilyFftRoundoffError family ε = p09FourierTransform (δ ε) ∧
        p09ComplexRms (δ ε) =
          p09ComplexRms (p09FamilyFftRoundoffError family ε) /
            Real.sqrt (n : ℝ)) ∧
      ∀ ε, ε.1 ≤ forward.radius →
        p09ComplexRms (δ ε) ≤
            ε.1 * p09K plan γ * p09ComplexRms family.input +
              (forward.secondOrderCoeff * ε.1 ^ 2) /
                Real.sqrt (n : ℝ) ∧
          p09ComplexMax (δ ε) ≤
            ε.1 * Real.sqrt (n : ℝ) * p09K plan γ *
                p09ComplexRms family.input +
              forward.secondOrderCoeff * ε.1 ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
