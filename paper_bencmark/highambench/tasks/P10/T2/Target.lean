import HighamBench.P10Definitions

namespace HighamBench

/-- P10-T2: the complete first-order normwise product-error rule (8). -/
theorem p10_t2_first_order_product_error {n : ℕ}
    (run : P10FirstOrderProductRun n) :
    run.matrixNorm.value (p10FirstOrderProductError run) ≤
      p10FirstOrderProductErrorBudget run := by
  -- PROOF_START
  sorry

end HighamBench
