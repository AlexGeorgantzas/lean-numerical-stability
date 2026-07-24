import NumStability.Source.Higham.Chapter26.AlternatingDirections.CrudeLineSearch

/-!
# Higham Chapter 26 crude line-search smoke test
-/

#check NumStability.higham26ADInitialStep
#check NumStability.higham26ADDirectedStep
#check NumStability.higham26ADDoubleSearch
#check NumStability.higham26ADDoubleSearch_eq_pow
#check NumStability.higham26ADCrudeAlpha
#check NumStability.higham26ADCrudeAlpha_eq_zero_or_pow
#check NumStability.higham26ADCrudeSearch
#check NumStability.higham26ADCrudeSweep_nondecreasing
