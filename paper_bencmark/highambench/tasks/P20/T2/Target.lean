import HighamBench.P20Definitions

namespace HighamBench

/-- P20-T2: the scaled input-conversion error satisfies equation (3.13). -/
theorem p20_t2_scaled_input_error {n : ℕ} {ι : Type*}
    (model : P20Model1 ι) (t : ι) (x y : Fin n → ℝ)
    (lambda mu : ℝ) (hn : 0 < n)
    (hx : 0 < p20InfNormVec x) (hy : 0 < p20InfNormVec y)
    (hlambda : p20MaximalPowerTwoScale
      (p20ModelScalingThreshold n model t) (p20InfNormVec x) lambda)
    (hmu : p20MaximalPowerTwoScale
      (p20ModelScalingThreshold n model t) (p20InfNormVec y) mu) :
    |p20InputStageError model t lambda mu x y| ≤
      p20InputStageErrorEnvelope
        (p20InputUnitRoundoff model t)
        (p20InputUnderflowEnvelope model t)
        (p20ModelScalingThreshold n model t) x y := by
  -- PROOF_START
  sorry

end HighamBench
