import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import NumStability.Algorithms.HighamChapter15BoydBridges
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Uniqueness.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydUniqueness
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydUniqueness
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydUniqueness

/-!
# HighamChapter15BoydUniqueness (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydUniqueness`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
