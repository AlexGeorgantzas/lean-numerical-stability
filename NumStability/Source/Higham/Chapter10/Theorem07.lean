import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Source.Higham.Chapter10.Theorem07.Core.Results

/-!
# Theorem07

Declaration-free source aggregate after wave R04. Every declaration
moved unchanged to its routed child; this module imports the canonical
children so existing imports keep resolving.
-/
