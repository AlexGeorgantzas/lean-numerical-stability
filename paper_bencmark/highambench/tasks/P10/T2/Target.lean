import HighamBench.P10Definitions

namespace HighamBench

/-- P10-T2: exact finite completion of the first-order product-error rule (8). -/
theorem p10_t2_product_error_with_cross_term {n : ℕ}
    (A dA B dB E : P10Matrix n) :
    p10FrobNorm (p10ProductErrorExpansion n A dA B dB E) ≤
      p10FrobNorm E +
        p10FrobNorm A * p10FrobNorm dB +
        p10FrobNorm dA * p10FrobNorm B +
        p10FrobNorm dA * p10FrobNorm dB := by
  -- PROOF_START
  sorry

end HighamBench
