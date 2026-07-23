import NumStability.Algorithms.Summation

/-!
# Complete summation aggregate smoke test

Checks that the published family entry point retains both reusable and
source-correspondence declarations moved during the split.
-/

#check NumStability.fl_recursiveSum
#check NumStability.recursiveSum_problem43_abs_error_bound
#check NumStability.fl_pairwiseSum
#check NumStability.fl_pairwiseSumSixDisplayed
#check NumStability.fl_insertionSumList
#check NumStability.fl_insertionPowersFour_eq_recursiveSum
