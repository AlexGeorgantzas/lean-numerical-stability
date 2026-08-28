import HighamBench.P13Definitions

namespace HighamBench

/-- P13-T1: Lemma 2.2 identifies Definition 2.1's componentwise perturbation
condition number with the closed-form quotient in (2.2), which is at least
one. -/
theorem p13_t1_condition_ge_one {n : ℕ} (problem : P13LagrangeProblem n)
    (hvalue : p13LagrangeValue problem ≠ 0) :
    p13IsComponentwiseConditionNumber
        (p13LagrangeBasisValues problem) problem.data
        (p13Condition (p13LagrangeBasisValues problem) problem.data) ∧
      1 ≤ p13Condition (p13LagrangeBasisValues problem) problem.data := by
  -- PROOF_START
  sorry

end HighamBench
