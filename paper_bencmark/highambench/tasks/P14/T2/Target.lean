import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

/-- P14-T2: exact finite componentwise form of Theorem 3.3.  When both
operation radii equal `u`, the numerator and denominator radii have
first-order sum `(n+3)u`, as in the paper. -/
theorem p14_t2_basic_softmax_component_error {n : ℕ}
    (fp : P14StandardAddModel) (x wHat : Fin n → ℝ) (j : Fin n)
    (epsilonExp epsilonDiv deltaDiv : ℝ)
    (hepsilonExp : 0 ≤ epsilonExp)
    (hepsilonDiv : 0 ≤ epsilonDiv)
    (hdeltaDiv : |deltaDiv| ≤ epsilonDiv)
    (hwHat : ∀ i, 0 ≤ wHat i)
    (hexp : ∀ i,
      |wHat i - Real.exp (x i)| ≤ epsilonExp * Real.exp (x i))
    (hvalid : P14GammaValid fp.u n)
    (hsmall : p14DenominatorRadius fp.u n epsilonExp < 1) :
    |p14ComputedSoftmax fp wHat deltaDiv j - p14Softmax x j| /
        |p14Softmax x j| ≤
      (p14NumeratorRadius epsilonExp epsilonDiv +
          p14DenominatorRadius fp.u n epsilonExp) /
        (1 - p14DenominatorRadius fp.u n epsilonExp) := by
  -- PROOF_START
  sorry

end HighamBench
