import NumStability.Source.Higham.Chapter01.Section12.InstabilityWithoutCancellation.PivotingExample

/-!
# R03 canonical-only test — `PivotingExample`

Imports exactly the canonical destination and checks all 6
routed public declarations. No historical owner import.
-/

#check @NumStability.noPivotIeeeSinglePartialPivotRoundedLUBackwardError
#check @NumStability.noPivotPartialPivotLUBackwardError_zero
#check @NumStability.noPivotPartialPivotLUFactSpec
#check @NumStability.noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds
#check @NumStability.noPivotPartialPivotRoundedLUBackwardError
#check @NumStability.noPivotPartialPivotSwap_bijective
