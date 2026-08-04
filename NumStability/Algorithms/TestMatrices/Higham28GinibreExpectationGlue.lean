import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreExpectationGlue

/-!
# Higham28GinibreExpectationGlue (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreExpectationGlue`
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

/-- The normalized determinant-moment increment is exactly the two-step
increment of the finite real-Ginibre closed form. -/
theorem ginibreCorollary31Factor_mul_increment_eq_closedForm_shift
    (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor (m + 2) *
        ginibreAbsoluteCharacteristicMomentIncrement (m + 1) =
      realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m := by
  rw [ginibreCorollary31Factor_mul_increment (m + 1) (Nat.zero_lt_succ m)]
  push_cast
  rw [show (m : ℝ) + 1 - 1 / 2 = (m : ℝ) + 1 / 2 by ring]
  exact (realGinibreExpectedCountClosedForm_shift_two m hm).symm

end NumStability

end
