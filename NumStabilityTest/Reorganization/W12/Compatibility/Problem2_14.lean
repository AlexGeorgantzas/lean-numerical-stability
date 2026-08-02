import NumStability.Analysis.Problem2_14

/-!
# Problem2_14 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.problem2_14_ieeeDoubleKahanEstimate
#check @NumStability.FloatingPointFormat.problem2_14_ieeeSingleKahanEstimate
