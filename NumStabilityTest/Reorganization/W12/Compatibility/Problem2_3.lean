import NumStability.Analysis.Problem2_3

/-!
# Problem2_3 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.problem2_3_subnormalBlockScale
#check @NumStability.FloatingPointFormat.Problem2_3IeeeSingleAdjacentGap
#check @NumStability.FloatingPointFormat.problem2_3_adjacentSingleGapLeftValue
