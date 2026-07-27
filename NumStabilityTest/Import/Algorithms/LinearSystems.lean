import NumStability.Algorithms.LinearSystems

/-!
# Linear-systems aggregate import smoke test

The aggregate must expose both the reusable Block LU foundations and the
canonical triangular-system family.
-/

#check NumStability.blockMaxNorm
#check NumStability.MatMulFirstOrderSpec
#check NumStability.fl_backSub
#check NumStability.triangularSolve_backward_error
