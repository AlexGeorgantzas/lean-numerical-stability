import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization

/-!
# Recursive block LU factorization import smoke test

This test imports only the canonical recursive-factorization leaf and checks
all six reviewed public declarations. The two finite-sum helpers remain
private implementation details.
-/

#check NumStability.blockLUOneStepL
#check NumStability.blockLUOneStepU
#check NumStability.blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail
#check NumStability.blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail
#check NumStability.blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail
#check NumStability.block_lu_one_step
