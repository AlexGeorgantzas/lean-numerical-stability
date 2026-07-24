import NumStability.FloatingPoint.IEEE.NaiveMaximum

/-!
# Naive IEEE maximum canonical import smoke test
-/

#check NumStability.ieeeNaiveMax
#check NumStability.ieeeNaiveMax_finite_finite_eq_max
#check NumStability.ieeeNaiveMax_left_nan
#check NumStability.ieeeNaiveMax_right_nan
#check NumStability.ieeeNaiveMax_not_nan_propagating
