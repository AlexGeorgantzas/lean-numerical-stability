import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Cauchy.Basic
import NumStability.Analysis.TestMatrices.Companion.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Orthogonal.Basic
import NumStability.Analysis.TestMatrices.Pascal.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Basic
import NumStability.Analysis.TestMatrices.Toeplitz.Basic
import NumStability.Source.Higham.Chapter28.Equation01.HilbertInverse.Basic
import NumStability.Source.Higham.Chapter28.Equation02.ExactHilbertDeterminant.Basic
import NumStability.Source.Higham.Chapter28.Equation03.HilbertCholeskyFactor.Basic
import NumStability.Source.Higham.Chapter28.Equation04.HilbertCholeskyInverse.Basic

/-!
# Higham28 (compatibility module)

Import-only module retained so existing imports of `NumStability.Algorithms.TestMatrices.Higham28`
keep resolving. Every declaration moved unchanged to the canonical
modules imported above. The module's own original imports are
re-stated so consumers reaching an identifier transitively through
this path still see the same surface.
-/
