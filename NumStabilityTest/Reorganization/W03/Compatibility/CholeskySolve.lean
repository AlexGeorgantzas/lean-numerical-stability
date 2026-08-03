import NumStability.Algorithms.Cholesky.CholeskySolve

/-!
# CholeskySolve old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W03, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.cholesky_solve_backward_error
#check @NumStability.cholesky_solve_spd_backward_stable
#check @NumStability.cholesky_solve_backward_error_expanded
