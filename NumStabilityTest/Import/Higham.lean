import NumStability.Higham

/-!
# Higham correspondence entry-point smoke test

Ensure the historical Higham entry point forwards both transitional source
modules and chapters already moved below `NumStability.Source.Higham`.
-/

#check NumStability.FloatingPointFormat.problem2_4_theorem2_3_nearest_finite
#check NumStability.higham14_hadamardConditionNumberRaw_negative_one_counterexample
#check NumStability.higham24_theorem24_3_literal_forward_error_multiple_kappa_u
#check NumStability.higham25NewtonEquation
