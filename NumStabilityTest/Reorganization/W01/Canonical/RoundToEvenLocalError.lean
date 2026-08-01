import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError

/-!
# RoundToEvenLocalError canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.finiteRoundToModeOp_nearestEven
#check @NumStability.FloatingPointFormat.finiteRoundToEvenSqrt
