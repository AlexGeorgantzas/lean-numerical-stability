import NumStability.Algorithms.LU.BlockLU

/-!
# Historical BlockLU old-only import smoke test

This test deliberately imports only the historical BlockLU path. It verifies
that Phase 12A extraction preserves representatives from every migrated
surface formerly declared by or available through that module, including the
safe reusable Phase 12B slices.
-/

#check NumStability.FirstOrderLe
#check NumStability.maxEntryNorm
#check NumStability.maxEntryNormRect
#check NumStability.blockMaxNorm
#check NumStability.IsBlockDiagDomCol
#check NumStability.BlockLUFactSpec
#check NumStability.BlockLUBackwardError
#check NumStability.MatMulFirstOrderSpec
#check NumStability.growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
#check NumStability.blockMatrixNonsingular_of_posDef_flat
#check NumStability.higham13_maxNorm_vecResidual_lift
#check NumStability.blockSchur
#check NumStability.dhsBlockForwardConventionalSolution
#check NumStability.blockErrorDelta
#check NumStability.higham13_theta_conventional_isBigO_cubic
