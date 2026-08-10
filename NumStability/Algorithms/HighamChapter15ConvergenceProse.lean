import Mathlib.Order.Fin.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements
import NumStability.Algorithms.PNormPowerMethodGeneralP
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.Corrections.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.EndpointTermination.ConvergenceStatements
import NumStability.Source.Higham.Chapter15.Section02.Boyd.GlobalConvergence.ConvergenceStatements

/-!
# HighamChapter15ConvergenceProse (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.HighamChapter15ConvergenceProse`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
