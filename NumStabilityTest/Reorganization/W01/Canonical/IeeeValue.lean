import NumStability.Analysis.FloatingPointArithmetic.IeeeValue

/-!
# IeeeValue canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.IeeeValue.nan_isNaN
#check @NumStability.IeeeValue.isNaN
