import Mathlib.Analysis.InnerProductSpace.NormPow
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormGeneral
import NumStability.Algorithms.PNormPowerMethod
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormGeneral
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormGeneral

/-!
# PNormPowerMethodGeneralP (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.PNormPowerMethodGeneralP`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
