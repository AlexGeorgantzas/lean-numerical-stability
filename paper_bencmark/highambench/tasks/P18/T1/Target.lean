import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T1: exact norm inequality behind the one-step decomposition
`E = E_sch + E_per` following equation (3.3). -/
theorem p18_t1_scheme_perturbation_error_split {n : ℕ}
    (schemeError perturbationError : Fin n → ℝ) :
    p18VecNorm2 (p18Add schemeError perturbationError) ≤
      p18VecNorm2 schemeError + p18VecNorm2 perturbationError := by
  -- PROOF_START
  sorry

end HighamBench
