import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.Gamma
import NumStability.Algorithms.TestMatrices.Higham28GinibreCharacteristicProduct
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedScalar

/-!
# Higham28GinibreSignedScalar (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28GinibreSignedScalar`
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

open MeasureTheory ProbabilityTheory Set Real Filter

open scoped BigOperators

/-- The characteristic-product integral is the scalar kernel evaluated at
the product of its two spectral parameters. -/
theorem integral_realGinibre_characteristicProduct_eq_kernel
    (m : ℕ) (u x : ℝ) :
    (∫ A : RSqMat m,
        (u • (1 : RSqMat m) - A).det *
          (x • (1 : RSqMat m) - A).det
      ∂realGinibreMeasure m) =
      ginibreCharacteristicProductKernel m (u * x) := by
  exact integral_realGinibre_characteristicProduct m u x

end NumStability

end
