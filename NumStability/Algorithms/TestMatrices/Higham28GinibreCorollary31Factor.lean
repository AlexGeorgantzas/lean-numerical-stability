import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreProjectiveIntegral
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreCorollary31Factor

/-!
# Higham28GinibreCorollary31Factor (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- Integral form of the exact Corollary 3.1 normalization. -/
theorem gaussianZeroPow_mul_integral_ginibreProjectiveWeight (n : ℕ) :
    (gaussianPDFReal 0 1 0) ^ n *
        (∫ y : Fin n → ℝ,
          (1 + ∑ i, y i ^ 2) ^ (-(((n : ℝ) + 1) / 2))) =
      ginibreCorollary31Factor (n + 1) := by
  rw [integral_ginibreProjectiveWeight,
    gaussianZeroPow_mul_projectiveConstant]

end NumStability

end
