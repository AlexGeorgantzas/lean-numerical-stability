import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.Environment

/-!
# Environment canonical-import test

Imports exactly one Higham Chapter 2 correspondence module, so no sibling import can supply the
declarations checked below.
-/

#check @NumStability.FloatingPointFormat.fortranEpsilon_pos
#check @NumStability.FloatingPointFormat.fortranEpsilon
