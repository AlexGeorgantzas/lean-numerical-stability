import NumStability.Analysis.FloatingPointArithmetic.Format

/-!
# Format canonical-import test

Imports exactly one reusable floating-point module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.t_pos
#check @NumStability.FloatingPointFormat.t
