import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure

/-!
# R09 old_only test

isolated historical import preserves the exact supported declaration surface
-/

#check @NumStability.expectedRealEigenvalueCount_eq_lebesgue
#check @NumStability.integrable_realGinibreDensityReal
#check @NumStability.measurable_realGinibreDensityReal
#check @NumStability.realGinibreLebesgueMeasure
#check @NumStability.realGinibreLebesgueMeasure_absolutelyContinuous
#check @NumStability.realGinibreMeasure_absolutelyContinuous_lebesgue
#check @NumStability.realGinibreMeasure_eq_withDensity
