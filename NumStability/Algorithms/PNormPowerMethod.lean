import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm01.PNormPowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation02.Subgradient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Equation04.NormalizedDualDiscrepancy.Basic
import NumStability.Source.Higham.Chapter15.Equation05.SubgradientInequality.Basic
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# PNormPowerMethod (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.PNormPowerMethod`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
