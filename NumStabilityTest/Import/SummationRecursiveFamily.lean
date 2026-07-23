import NumStability.Algorithms.Summation.Recursive

/-!
# Recursive summation family smoke test

Checks that the complete family entry point exposes both its reusable core and
the supported Higham Problem 4.3 correspondence.
-/

#check NumStability.fl_recursiveSum
#check NumStability.recursiveSum_problem43_abs_error_bound
