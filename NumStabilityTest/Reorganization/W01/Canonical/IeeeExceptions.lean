import NumStability.Analysis.FloatingPointArithmetic.IeeeExceptions

/-!
# IeeeExceptions canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.ieeeInexactResult_value
#check @NumStability.ieeeInexactResult
