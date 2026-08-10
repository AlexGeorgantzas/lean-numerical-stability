import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import NumStability.Algorithms.HighamChapter15BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydLocal
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydLocal
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydLocal
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal

/-!
# HighamChapter15BoydSourceLocal (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydSourceLocal`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
