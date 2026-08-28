import HighamBench.P07Definitions

namespace HighamBench

/-- P07-T1: Lemma 3.2, including both full column rank of the computed
forward-substitution output and the complete quantitative condition-number
bound in terms of the exact `epsilon_2`. -/
theorem p07_t1_perturbed_preconditioned_map_injective
    {m s n : ℕ}
    (pre : P07Lemma31ComputedPreconditioner m s n)
    (model : P07ScalarArithmeticModel)
    (run : P07Lemma32ForwardRun pre model)
    (exactData : P07MatrixPseudoinverseSpectralData
      (p07ExactPreconditionedMatrix pre))
    (errorSpectrum : P07RectSpectralExtrema run.DeltaY)
    (computedData : P07MatrixPseudoinverseSpectralData
      run.forwardSubstitution.output)
    (hsmall : p07Lemma32Epsilon exactData errorSpectrum < 1) :
    Function.Injective (p07MatVec run.forwardSubstitution.output) ∧
      p07ConditionNumber2 computedData ≤
        (p07ConditionNumber2 exactData +
            p07Lemma32Epsilon exactData errorSpectrum) /
          (1 - p07Lemma32Epsilon exactData errorSpectrum) := by
  -- PROOF_START
  sorry

end HighamBench
