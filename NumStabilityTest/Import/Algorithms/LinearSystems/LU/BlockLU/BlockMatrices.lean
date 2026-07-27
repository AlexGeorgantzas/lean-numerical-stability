import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices

/-!
# Block-matrix foundations import smoke test

This test imports only the canonical declaration-bearing leaf.
-/

#check NumStability.idBlock
#check NumStability.zeroBlock
#check NumStability.blockMul
#check NumStability.blockMatProd
#check NumStability.blockMaxNorm
#check NumStability.blockInfNorm
#check NumStability.blockMaxNorm_le_blockInfNorm
#check NumStability.blockMaxNorm_le_maxEntryNorm_of_reindex_eq
