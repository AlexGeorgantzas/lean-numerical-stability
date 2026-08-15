import HighamBench.P15Definitions

namespace HighamBench

/-- P15-T1: the Frobenius norm is submultiplicative, the first norm property
listed in Section 2.1 and used throughout the paper's error analysis. -/
theorem p15_t1_frobenius_submultiplicative {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p) :
    p15RectFrobNorm (p15RectMatMul A B) ≤
      p15RectFrobNorm A * p15RectFrobNorm B := by
  -- PROOF_START
  sorry

end HighamBench
