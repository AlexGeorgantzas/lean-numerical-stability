import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T1: the normwise backward error of a computed candidate is exactly its
normalized residual. `IsLeast` states both that the displayed value is attained
by one shared relative perturbation level and that every admissible level is at
least as large. -/
theorem p16_t1_normwise_backward_error_formula {n : ℕ}
    (A : P16Matrix n) (b xHat : P16Vector n)
    (hA : p16IsNonsingular A) (hb : b ≠ 0) :
    IsLeast
      {epsilon : ℝ | p16NormwiseBackwardErrorAdmissible A b xHat epsilon}
      (p16NormalizedResidual A b xHat) := by
  -- PROOF_START
  sorry

end HighamBench
