import NumStability.Algorithms.LinearSystems.LU.BlockLU

/-!
# Block LU aggregate import smoke test

This test imports only the canonical reusable Block LU aggregate and checks
representatives from both Phase 12A declaration-bearing children.
-/

#check NumStability.idBlock
#check NumStability.blockMaxNorm
#check NumStability.blockMaxNorm_le_blockInfNorm
#check NumStability.MatMulFirstOrderBound
#check NumStability.MatMulFirstOrderSpec
#check NumStability.DiagonalBlockSolveFirstOrderSpec
