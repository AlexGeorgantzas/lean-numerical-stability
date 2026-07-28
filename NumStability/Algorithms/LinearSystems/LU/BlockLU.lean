import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FactorizationError
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError

/-!
# Block LU algorithms

Declaration-free aggregate for the reusable Block LU foundations extracted in
Phase 12A and the completed reusable Phase 12B slices, including recursive
one-step factorization. Later Phase 12 slices extend this family without
introducing numbered-source correspondence into the reusable import surface.
-/
