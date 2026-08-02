import NumStability.Analysis.FloatingPointArithmetic.StandardModel

/-!
# Standard-model reusable-import test

Imports exactly the reusable standard-model module so no source wrapper or
sibling module can supply the checked declarations.
-/

#check @NumStability.FloatingPointFormat.finiteNormalFl_spec
#check @NumStability.inverseRelErrorModel
