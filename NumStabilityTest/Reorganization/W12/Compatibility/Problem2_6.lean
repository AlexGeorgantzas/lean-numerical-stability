import NumStability.Analysis.Problem2_6

/-!
# Problem2_6 old-import test

Imports only the historical path. The declarations below moved to canonical
modules during wave W12, so this compiles only if the compatibility module
still re-exports them at their original names.
-/

#check @NumStability.FloatingPointFormat.integerIntervalRepresentable
#check @NumStability.FloatingPointFormat.problem2_6_ieeeDouble_two_pow_53_finiteSystem
#check @NumStability.FloatingPointFormat.problem2_6_ieeeSingle_two_pow_24_finiteSystem
