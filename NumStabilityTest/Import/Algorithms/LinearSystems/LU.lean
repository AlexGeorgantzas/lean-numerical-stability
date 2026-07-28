import NumStability.Algorithms.LinearSystems.LU

/-!
# LU aggregate import smoke test

This test imports only the canonical reusable LU aggregate.
-/

#check NumStability.blockMaxNorm
#check NumStability.blockMaxNorm_le_blockInfNorm
#check NumStability.IsBlockDiagDomCol
#check NumStability.BlockLUFactSpec
#check NumStability.BlockLUBackwardError
#check NumStability.MatMulFirstOrderSpec
#check NumStability.DiagonalBlockSolveFirstOrderSpec
#check NumStability.growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
#check NumStability.blockMatrixNonsingular_of_posDef_flat
#check NumStability.higham13_maxNorm_vecResidual_lift
#check NumStability.blockSchur
#check NumStability.dhsBlockForwardConventionalSolution
