import NumStability.Analysis.Problem2_12

/-!
# Problem2_12 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.problem2_12_ieeeDouble_one_normalized
#check @NumStability.FloatingPointFormat.problem2_12_ieeeDouble_one_finiteSystem
#check @NumStability.FloatingPointFormat.problem2_12_ieeeDouble_rounds_one_to_self
