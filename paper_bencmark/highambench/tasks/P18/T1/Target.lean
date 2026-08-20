import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T1: the exact one-step decomposition `E = E_sch + E_per` following
equation (3.3), and its Euclidean-norm consequence. -/
theorem p18_t1_scheme_perturbation_error_split {n s : ℕ}
    (run : P18AdditiveRKOneStepRun n s) :
    p18TotalOneStepError run =
        p18Add (p18SchemeOneStepError run)
          (p18PerturbationOneStepError run) ∧
      p18VecNorm2 (p18TotalOneStepError run) ≤
        p18VecNorm2 (p18SchemeOneStepError run) +
          p18VecNorm2 (p18PerturbationOneStepError run) := by
  -- PROOF_START
  sorry

end HighamBench
