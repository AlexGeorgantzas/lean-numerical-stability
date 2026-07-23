import NumStability.Analysis.Summation.ErrorBounds

/-!
# Reusable summation error-bound import smoke test

This test imports the conditioning and rounded-fold error API directly,
without reaching any source-owned module.
-/

#check NumStability.summationConditionNumber_eq_one_iff_oneSigned
#check NumStability.fl_sum_error_tight
