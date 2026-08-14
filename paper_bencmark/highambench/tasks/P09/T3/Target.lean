import HighamBench.P09Definitions

namespace HighamBench

/-- P09-T3: Theorem 2(a) for the linked nested complex FFT. The exact
telescoping identity is retained, and the source's final `O(ε²)` is the
explicit finite coefficient `p09TheoremTwoRemainderCoeff`. -/
theorem p09_t3_multidimensional_rms_error_bound
    {m : ℕ} [NeZero m]
    (plan : P09MultidimensionalFftPlan m) (model : P09WilkinsonModel)
    (run : P09MultidimensionalFftRun plan model)
    (certificate : P09TheoremTwoRmsCertificate run)
    (hexactOutput : 0 < p09MultiRms (p09MultiExactOutput run)) :
    p09MultiFftRoundoffError run =
        p09MultiVectorSum (fun i ↦ p09PropagatedAxisError run i) ∧
      p09MultiRms (p09MultiFftRoundoffError run) /
          p09MultiRms (p09MultiExactOutput run) ≤
        model.epsilon *
            (∑ i : Fin m, p09AxisK (plan.axis i) model.gamma) +
          (p09TheoremTwoRemainderCoeff certificate /
              p09MultiRms (p09MultiExactOutput run)) * model.epsilon ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
