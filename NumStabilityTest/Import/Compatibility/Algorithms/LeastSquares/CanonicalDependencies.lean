import NumStability.Algorithms.Cholesky.CholeskySolve
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.QR.Higham19
import NumStability.Algorithms.QR.Higham19Alg12MGSRepair
import NumStability.Algorithms.QR.Higham19Alg12MGSRounded
import NumStability.Algorithms.QR.Higham19Labels
import NumStability.Algorithms.QR.Higham19Thm6ColPivot
import NumStability.Algorithms.QR.Higham19Thm6CoxHigham
import NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete
import NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged
import NumStability.Algorithms.QR.Higham19Thm6RowSpecific
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core
import NumStability.Algorithms.Underdetermined.Higham21ProjectorNorm
import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve
import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec
import NumStability.Analysis.HighamChapter7
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Canonical dependency smoke tests for the Chapter 20 forwarding surface

The historical LSQ wrappers intentionally restate their transitive import
surface.  Keep the corresponding canonical entry points directly reachable
from the test graph so the compatibility gate checks each one independently.
-/
