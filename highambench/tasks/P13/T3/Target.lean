import HighamBench.P13Definitions

namespace HighamBench

/-- P13-T3: Theorem 4.1 for the directly weighted second barycentric formula,
including its genuine quadratic remainder and first-order sharpness claim. -/
theorem p13_t3_barycentric_forward_bound
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (problem : P13SecondBarycentricProblem n)
    (u : ι → ℝ)
    (run : ∀ t, P13SecondBarycentricExecution problem (u t))
    (hu : Filter.Tendsto u l (nhds 0))
    (hnumerator : p13SecondBarycentricNumerator problem ≠ 0)
    (hdenominator : p13SecondBarycentricDenominator problem ≠ 0) :
    let conditionData := p13SecondBarycentricDataCondition problem
    let conditionOne := p13SecondBarycentricOneCondition problem
    (∀ᶠ t in l,
      p13SecondBarycentricRelativeError (run t) ≤
        p13SecondBarycentricFiniteEnvelope n (u t)
          conditionData conditionOne) ∧
    (∀ᶠ t in l,
      p13SecondBarycentricFiniteEnvelope n (u t)
          conditionData conditionOne =
        u t * p13SecondBarycentricFirstOrderCoefficient n
          conditionData conditionOne +
        p13SecondBarycentricForwardRemainder n
          conditionData conditionOne (u t)) ∧
    (fun t =>
      p13SecondBarycentricForwardRemainder n
        conditionData conditionOne (u t)) =O[l]
      (fun t => (u t) ^ 2) ∧
    P13SecondBarycentricFirstOrderSharp problem := by
  -- PROOF_START
  sorry

end HighamBench
