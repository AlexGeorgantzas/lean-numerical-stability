import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError

/-!
# NearestRoundingError canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.finiteRoundToEven_neg
#check @NumStability.FloatingPointFormat.finiteNearestFl
