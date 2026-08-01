import NumStability.Analysis.FloatingPointArithmetic.IeeeOperations

/-!
# IeeeOperations canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.ieeeRoundToModeOpResult_nearestEven
#check @NumStability.FloatingPointFormat.ieeeRoundToModeOpResult
