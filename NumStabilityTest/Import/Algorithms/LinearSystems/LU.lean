import NumStability.Algorithms.LinearSystems.LU

/-!
# LU aggregate import smoke test

This test imports only the canonical reusable LU aggregate.
-/

#check NumStability.blockMaxNorm
#check NumStability.blockMaxNorm_le_blockInfNorm
#check NumStability.MatMulFirstOrderSpec
#check NumStability.DiagonalBlockSolveFirstOrderSpec
