import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo

/-!
# R09 old_only test

isolated historical import preserves the exact supported declaration surface
-/

#check @NumStability.expectedRealEigenvalueCount_eq_closedForm_two
#check @NumStability.expectedRealEigenvalueCount_two
#check @NumStability.measurableSet_realGinibreTwoNonnegativeDiscriminantSet
#check @NumStability.measurable_ginibreTwoEntryVector
#check @NumStability.realGinibreMeasure_two_discriminant_nonnegative_real
#check @NumStability.realGinibreMeasure_two_map_ginibreTwoEntryVector
