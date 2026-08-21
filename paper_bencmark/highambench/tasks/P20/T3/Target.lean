import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T3: Theorem 4.1 and equations (4.32)--(4.33). A Model-1 execution of
the scaled p-word algorithm (4.29)--(4.31) satisfies the four-term normwise
forward-error bound (4.32), modulo the second-order terms hidden by `lesssim`.
The second conclusion identifies the two additional narrow-range terms over
the range-unrestricted coefficient (4.33); it is not an exact error bound. -/
theorem p20_t3_multiword_forward_error
    {m n q p : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (execution : P20Theorem41Execution m n q p ι l) :
    p20FirstOrderLeAt l (p20MultiwordPrecisionScale execution.run)
        (p20MultiwordForwardError execution.run)
        (fun t =>
          p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20AccumUnitRoundoff execution.run.model t)
              (p20ModelScalingThreshold n execution.run.model t)
              (p20InputUnderflowEnvelope execution.run.model t)
              (p20AccumUnderflowEnvelope execution.run.model t))
            execution.run.A execution.run.B) ∧
      ∀ t,
        p20MultiNarrowCoefficient n p
            (p20InputUnitRoundoff execution.run.model t)
            (p20AccumUnitRoundoff execution.run.model t)
            (p20ModelScalingThreshold n execution.run.model t)
            (p20InputUnderflowEnvelope execution.run.model t)
            (p20AccumUnderflowEnvelope execution.run.model t) =
          p20MultiRangeFreeCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20AccumUnitRoundoff execution.run.model t) +
            p20MultiInputUnderflowCoefficient n p
              (p20InputUnitRoundoff execution.run.model t)
              (p20ModelScalingThreshold n execution.run.model t)
              (p20InputUnderflowEnvelope execution.run.model t) +
            p20MultiAccumUnderflowCoefficient n p
              (p20ModelScalingThreshold n execution.run.model t)
              (p20AccumUnderflowEnvelope execution.run.model t) := by
  -- PROOF_START
  sorry

end HighamBench
