import NumStability.Algorithms.LinearSystems

/-!
# Linear-systems aggregate import smoke test

The aggregate must expose both the reusable Block LU foundations and the
canonical triangular-system family.
-/

#check NumStability.blockMaxNorm
#check NumStability.IsBlockDiagDomCol
#check NumStability.BlockLUBackwardError
#check NumStability.MatMulFirstOrderSpec
#check NumStability.growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio
#check NumStability.higham13_maxNorm_vecResidual_lift
#check NumStability.fl_backSub
#check NumStability.triangularSolve_backward_error
