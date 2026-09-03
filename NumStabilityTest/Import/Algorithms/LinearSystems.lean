import NumStability.Algorithms.LinearSystems

/-!
# Linear-systems aggregate import smoke test

The aggregate must expose both the reusable Block LU foundations and the
canonical triangular-system family.
-/

#check NumStability.blockMaxNorm
#check NumStability.IsBlockDiagDomCol
#check NumStability.BlockLUFactSpec
#check NumStability.BlockLUBackwardError
#check NumStability.MatMulFirstOrderSpec
#check NumStability.growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
#check NumStability.blockMatrixNonsingular_of_posDef_flat
#check NumStability.higham13_maxNorm_vecResidual_lift
#check NumStability.blockSchur
#check NumStability.block_lu_one_step
#check NumStability.dhsBlockForwardConventionalSolution
#check NumStability.fl_backSub
#check NumStability.triangularSolve_backward_error
#check NumStability.Ch11Closure.AasenDirect.flAasenInit
#check NumStability.Ch11Closure.BunchTriFactor.alpha_pos
#check NumStability.Ch11Closure.SparseSolve.bunchTriSparseSolveCoeff_nonneg
