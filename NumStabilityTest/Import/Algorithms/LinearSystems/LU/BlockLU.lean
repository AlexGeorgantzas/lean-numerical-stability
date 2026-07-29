import NumStability.Algorithms.LinearSystems.LU.BlockLU

/-!
# Block LU aggregate import smoke test

This test imports only the canonical reusable Block LU aggregate and checks
representatives from all fifteen declaration-bearing direct leaves and the
five unequal-order leaves exposed through the `VaryingBlocks` subaggregate.
-/

#check NumStability.idBlock
#check NumStability.blockMaxNorm
#check NumStability.blockMaxNorm_le_blockInfNorm
#check NumStability.IsBlockDiagDomCol
#check NumStability.BlockLUFactSpec
#check NumStability.BlockLUBackwardError
#check NumStability.MatMulFirstOrderBound
#check NumStability.MatMulFirstOrderSpec
#check NumStability.DiagonalBlockSolveFirstOrderSpec
#check NumStability.growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
#check NumStability.blockMatrixNonsingular_of_posDef_flat
#check NumStability.higham13_maxNorm_vecResidual_lift
#check NumStability.blockSchur
#check NumStability.block_lu_one_step
#check NumStability.dhsBlockForwardConventionalSolution
#check NumStability.Higham13CLMBlockNonsingular
#check NumStability.Higham13BlockSolveFamilySpec
#check NumStability.higham13_abs_entry_le_opNorm2
#check NumStability.matrix_posDef_to_isSymPosDef
#check NumStability.blockLUOneStepL_firstSplit_fromBlocks
#check NumStability.Higham13PositiveBlockOrders
#check NumStability.higham13VaryingBlockUnitLower_fromBlocks
#check NumStability.Higham13VaryingLeadingPrincipalNonsingular.of_det_of_schur
#check NumStability.Higham13VaryingBlockLUFactSpec.eq_step_of_tail_unique
#check NumStability.Higham13VaryingBlockLUExistsUnique
