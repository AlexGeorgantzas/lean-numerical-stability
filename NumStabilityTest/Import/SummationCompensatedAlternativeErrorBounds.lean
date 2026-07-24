import NumStability.Algorithms.Summation.Compensated.Alternative.ErrorBounds

/-!
# Alternative compensated-summation error-bound smoke test

Checks the reusable error-analysis leaf independently of source correspondence.
-/

#check NumStability.fl_alternativeCompensatedMainSum_add_exact_corrections_eq_sum_of_exact_steps
#check NumStability.alternativeCompensatedCorrectionRunningErrorBudget_of_exact_steps
#check NumStability.fl_alternativeCompensatedSum_exactWithUnitRoundoff
