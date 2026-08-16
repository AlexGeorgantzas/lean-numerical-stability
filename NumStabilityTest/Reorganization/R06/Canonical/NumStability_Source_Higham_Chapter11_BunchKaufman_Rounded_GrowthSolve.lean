import NumStability.Source.Higham.Chapter11.BunchKaufman.Rounded.GrowthSolve

/-!
# R06 canonical-only test — `GrowthSolve`

Imports exactly the canonical destination and checks all 4
routed public declarations. No historical owner import.
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.computedSolve_backward_error_normwise_forty
#check @NumStability.Higham11RoundedBunchKaufmanExecution.computedSolve_backward_error_normwise_forty_source
#check @NumStability.Higham11RoundedBunchKaufmanExecution.flatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
#check @NumStability.Higham11RoundedBunchKaufmanExecution.sourceFlatAbsProduct_le_forty_mul_dimension_mul_roundedGrowthFactor
