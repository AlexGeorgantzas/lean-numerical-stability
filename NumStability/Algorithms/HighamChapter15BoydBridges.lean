import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.Compact
import NumStability.Algorithms.HighamChapter15ConvergenceProse
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Duality.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.PNormPowerMethodRect
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.BoydInterface
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.BoydInterface
import NumStability.Source.Higham.Chapter15.Section02.Boyd.LocalConvergence.BoydInterface

/-!
# HighamChapter15BoydBridges (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.HighamChapter15BoydBridges`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
