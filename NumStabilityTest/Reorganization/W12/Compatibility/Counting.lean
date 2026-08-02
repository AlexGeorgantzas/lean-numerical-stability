import NumStability.Analysis.Counting

/-!
# Counting old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.signedParameterCount
#check @NumStability.FloatingPointFormat.subnormalValue_true_eq_iff
#check @NumStability.FloatingPointFormat.subnormalValue_false_eq_iff
