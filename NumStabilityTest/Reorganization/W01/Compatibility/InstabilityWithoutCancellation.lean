import NumStability.Analysis.InstabilityWithoutCancellation

/-!
# InstabilityWithoutCancellation old-import test

Imports only the historical path, proving the retained compatibility
module still resolves the declarations it used to own.
-/

#check @NumStability.repeatedSqrt
#check @NumStability.repeatedSquare
#check @NumStability.noPivotExampleA
