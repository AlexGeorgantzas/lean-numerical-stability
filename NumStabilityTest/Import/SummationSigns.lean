import NumStability.Analysis.Summation.Signs

/-!
# Reusable summation-sign import smoke test

This test imports the generic sign API without the broader error-bound layer,
protecting the narrow reusable import boundary.
-/

#check NumStability.OneSigned
#check NumStability.sum_abs_eq_abs_sum_iff_oneSigned
