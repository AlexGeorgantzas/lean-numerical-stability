import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T1: the exact one-step decomposition `E = E_sch + E_per` following
equation (3.3), linked to the additive output (3.1b). The final clause is a
separate consequence for every finite-coordinate additive observation; it
does not select a norm for the paper's abstract error symbols. -/
theorem p18_t1_scheme_perturbation_error_split
    {State : Type*} [AddCommGroup State] [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) :
    p18TotalOneStepError run =
        p18SchemeOneStepError run + p18PerturbationOneStepError run ∧
      p18PerturbationOneStepError run =
        p18PerturbationOutputExpansion run ∧
      ∀ {n : ℕ} (observe : State →+ (Fin n → ℝ)),
        p18VecNorm2 (observe (p18TotalOneStepError run)) ≤
          p18VecNorm2 (observe (p18SchemeOneStepError run)) +
            p18VecNorm2 (observe (p18PerturbationOneStepError run)) := by
  -- PROOF_START
  sorry

end HighamBench
