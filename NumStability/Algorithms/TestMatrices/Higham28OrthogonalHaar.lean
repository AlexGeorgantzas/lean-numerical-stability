import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.TestMatrices.Higham28OrthogonalSphere
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar

/-!
# Higham28OrthogonalHaar (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28OrthogonalHaar`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
