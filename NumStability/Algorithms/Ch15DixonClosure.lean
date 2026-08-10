import Mathlib.Analysis.Matrix.Order
import NumStability.Algorithms.Ch15CondEstimators
import NumStability.Algorithms.Ch15DixonProbability
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonCompletion
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Source.Higham.Chapter15.Theorem06.Dixon.Basic

/-!
# Ch15DixonClosure (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.Ch15DixonClosure`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
