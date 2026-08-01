import NumStability.Analysis.FloatingPointArithmetic.Rounding

/-!
# Rounding canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.finiteSystem_zero
#check @NumStability.FloatingPointFormat.finiteOverflowSaturation
