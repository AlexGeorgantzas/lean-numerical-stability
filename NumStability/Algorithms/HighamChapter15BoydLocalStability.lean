import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
import NumStability.Algorithms.HighamChapter15BoydBridges
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.BoydLocalStability
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydLocalStability

/-!
# HighamChapter15BoydLocalStability (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydLocalStability`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
