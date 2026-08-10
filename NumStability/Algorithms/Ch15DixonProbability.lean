import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import NumStability.Algorithms.Ch15CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates

/-!
# Ch15DixonProbability (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch15DixonProbability`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
