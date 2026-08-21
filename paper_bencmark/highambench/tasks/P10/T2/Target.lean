import HighamBench.P10Definitions

namespace HighamBench

/-- P10-T2: the complete first-order normwise product-error rule (8), with
the suppressed term interpreted uniformly as `O(epsilon^2)`. -/
theorem p10_t2_first_order_product_error {n : ℕ}
    (algorithm : P10StableMatrixMultiplication)
    (family : P10FirstOrderProductFamily algorithm n) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ epsilon : P10PositiveEpsilon, (epsilon : ℝ) ≤ radius →
          (algorithm.matrixNorm n).value
              (p10ProductFamilyError algorithm family epsilon) ≤
            p10ProductFamilyErrorBudget algorithm family epsilon +
              secondOrderCoeff * (epsilon : ℝ) ^ 2 := by
  -- PROOF_START
  sorry

end HighamBench
