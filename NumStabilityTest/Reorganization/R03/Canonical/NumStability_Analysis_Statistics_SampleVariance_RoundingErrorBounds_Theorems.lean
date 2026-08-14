import NumStability.Analysis.Statistics.SampleVariance.RoundingErrorBounds.Theorems

/-!
# R03 canonical-only test — `Theorems`

Imports exactly the canonical destination and checks all 7
routed public declarations. No historical owner import.
-/

#check @NumStability.flPrefixCorrectedSumSquaresStep_abs_error_le
#check @NumStability.flPrefixCorrectedSumSquaresStep_abs_error_le_prefix_succ
#check @NumStability.flPrefixCorrectedSumSquaresTrajectory_abs_error_le_budget
#check @NumStability.flPrefixMeanStep_abs_error_le
#check @NumStability.flPrefixMeanStep_abs_error_le_prefixMean_succ
#check @NumStability.flPrefixMeanTrajectory_abs_error_le_budget
#check @NumStability.flSampleVarianceUpdate_abs_error_le_budget
