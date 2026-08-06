import HighamBench.P16Definitions

namespace HighamBench

/-- P16-T1: a perturbed solve produces a residual bounded by the matrix and
right-hand-side perturbations, the exact estimate behind the normwise backward
error formula in Section 2. -/
theorem p16_t1_perturbed_solve_residual_bound {n : ℕ}
    (A deltaA : P16Matrix n) (b deltaB x : P16Vector n)
    (hsolve : p16MatVec (A + deltaA) x = b + deltaB) :
    p16VecNorm (p16Residual A b x) ≤
      p16FrobNorm deltaA * p16VecNorm x + p16VecNorm deltaB := by
  -- PROOF_START
  sorry

end HighamBench
