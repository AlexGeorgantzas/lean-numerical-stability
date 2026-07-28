import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FactorizationError
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting

/-!
# Block LU algorithms

Declaration-free aggregate for the reusable Block LU foundations extracted in
Phase 12A and the first Phase 12B wave. Later Phase 12 slices extend this family
without introducing numbered-source correspondence into the reusable import
surface.
-/
