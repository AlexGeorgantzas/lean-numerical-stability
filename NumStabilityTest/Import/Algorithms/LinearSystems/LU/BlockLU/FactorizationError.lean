import NumStability.Algorithms.LinearSystems.LU.BlockLU.FactorizationError

/-!
# Block LU factorization-error import smoke test

This test imports only the canonical declaration-bearing leaf and checks the
reviewed structure surface.
-/

#check NumStability.BlockLUBackwardError
#check NumStability.BlockLUBackwardError.L_diag
#check NumStability.BlockLUBackwardError.L_upper_zero
#check NumStability.BlockLUBackwardError.U_lower_zero
#check NumStability.BlockLUBackwardError.backward_bound
#check NumStability.BlockLUBackwardError.casesOn
#check NumStability.BlockLUBackwardError.mk
#check NumStability.BlockLUBackwardError.rec
#check NumStability.BlockLUBackwardError.recOn
