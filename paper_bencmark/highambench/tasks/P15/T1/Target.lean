import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T1: the Frobenius norm is submultiplicative, the first norm property
listed in Section 2.1 and used throughout the paper's error analysis. -/
theorem p15_t1_frobenius_submultiplicative {n : ℕ}
    (A B : P15Matrix n) :
    p15FrobNorm (p15MatMul A B) ≤ p15FrobNorm A * p15FrobNorm B := by
  -- PROOF_START
  sorry

end HighamBench
