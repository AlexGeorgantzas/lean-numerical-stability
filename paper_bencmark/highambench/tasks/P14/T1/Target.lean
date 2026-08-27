import HighamBench.P14Definitions

namespace HighamBench

open scoped BigOperators

/-- P14-T1: the positive exponential-evaluation and recursive-summation
analysis culminating in equation (3.3). -/
theorem p14_t1_positive_recursive_sum_relative_error
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P14BasicSumExecution x (u t))
    (hu : Filter.Tendsto u l (nhds 0)) :
    let exactSum := p14ExpSum x
    0 < exactSum ∧
    (∀ t i,
      |p14ComputedExp (run t) i - Real.exp (x i)| ≤
        u t * Real.exp (x i)) ∧
    (∀ᶠ t in l,
      |p14ExactComputedExpSum (run t) -
          p14RecursiveComputedExpSum (run t)| ≤
        gamma (u t) (n - 1) *
          ∑ i, |p14ComputedExp (run t) i|) ∧
    (∀ᶠ t in l,
      |p14BasicSumDelta (run t)| ≤
        p14BasicSumFiniteEnvelope n (u t) exactSum) ∧
    (∀ᶠ t in l,
      p14BasicSumFiniteEnvelope n (u t) exactSum =
        (n + 1 : ℝ) * u t * exactSum +
          p14BasicSumQuadraticRemainder n exactSum (u t)) ∧
    (fun t => p14BasicSumQuadraticRemainder n exactSum (u t)) =O[l]
      (fun t => (u t) ^ 2) ∧
    ∀ t,
      p14RecursiveComputedExpSum (run t) =
        exactSum + p14BasicSumDelta (run t) := by
  -- PROOF_START
  sorry

end HighamBench
