import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T2: Ramos's fictional-input backward-error interpretation on printed
page 768. For each actual error in one fixed operational FFT family, the
fictional input is selected after the precision and error are fixed. The
imported derivation combines the paper's separate block and twiddle estimates
`(3.6)`--`(3.8)` into Theorem 1(a). -/
theorem p09_t2_fictional_input_backward_error
    {n : ℕ} [NeZero n]
    (plan : P09MixedRadixFftPlan n) (γ : ℝ)
    (family : P09AsymptoticFftFamily plan γ) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ ε : P09PositiveEpsilon, ∃ δ : ZMod n → ℂ,
          p09FamilyFftRoundoffError family ε =
              p09FourierTransform δ ∧
            p09ComplexRms δ =
              p09ComplexRms
                  (p09FamilyFftRoundoffError family ε) /
                Real.sqrt (n : ℝ) ∧
            (ε.1 ≤ radius →
              p09ComplexRms δ ≤
                  ε.1 * p09K plan γ *
                      p09ComplexRms family.input +
                    (secondOrderCoeff * ε.1 ^ 2) /
                      Real.sqrt (n : ℝ) ∧
                p09ComplexMax δ ≤
                  ε.1 * Real.sqrt (n : ℝ) * p09K plan γ *
                      p09ComplexRms family.input +
                    secondOrderCoeff * ε.1 ^ 2) := by
  -- PROOF_START
  sorry

end HighamBench
