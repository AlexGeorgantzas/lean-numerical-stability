import NumStability.Analysis.InstabilityWithoutCancellation

/-!
# R03 historical-only test — `InstabilityWithoutCancellation`

Imports exactly the historical path; checks its preserved public
surface (6 declarations).
-/

#check @NumStability.noPivotIeeeSinglePartialPivotRoundedLUBackwardError
#check @NumStability.noPivotPartialPivotLUBackwardError_zero
#check @NumStability.noPivotPartialPivotLUFactSpec
#check @NumStability.noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds
#check @NumStability.noPivotPartialPivotRoundedLUBackwardError
#check @NumStability.noPivotPartialPivotSwap_bijective
