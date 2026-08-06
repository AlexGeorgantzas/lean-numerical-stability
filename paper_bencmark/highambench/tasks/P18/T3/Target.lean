import HighamBench.P18Definitions

namespace HighamBench

/-- P18-T3: exact smooth and nonsmooth perturbation envelopes for Method
4s3pC, together with their ordering on a normalized small time step. -/
theorem p18_t3_smooth_nonsmooth_method_error_bounds {n : ℕ}
    (h epsilon : ℝ) (scheme perturbation : Fin n → ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hepsilon : 0 ≤ epsilon) :
    p18VecNorm2 (p18SmoothMethodError h epsilon scheme perturbation) ≤
        h ^ 3 * (p18VecNorm2 scheme + epsilon * p18VecNorm2 perturbation) ∧
      p18VecNorm2 (p18NonsmoothMethodError h epsilon scheme perturbation) ≤
        h ^ 3 * p18VecNorm2 scheme +
          epsilon * h ^ 2 * p18VecNorm2 perturbation ∧
      h ^ 3 * (p18VecNorm2 scheme + epsilon * p18VecNorm2 perturbation) ≤
        h ^ 3 * p18VecNorm2 scheme +
          epsilon * h ^ 2 * p18VecNorm2 perturbation := by
  -- PROOF_START
  sorry

end HighamBench
