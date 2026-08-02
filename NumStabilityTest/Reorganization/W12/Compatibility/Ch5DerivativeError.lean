import NumStability.Algorithms.Ch5DerivativeError

/-!
# Ch5DerivativeError old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.ch5psi_AlternatingSignDesc
#check @NumStability.ch5deriv_value_forward_error_bound
#check @NumStability.ch5psi_polyDesc_eq_polyDescAbs_of_nonneg
