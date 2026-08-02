import NumStability.Analysis.Problem2_20

/-!
# Problem2_20 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.problem2_20_exactRatio
#check @NumStability.problem2_20_computedRatio
#check @NumStability.problem2_20_exactRatio_le_one
