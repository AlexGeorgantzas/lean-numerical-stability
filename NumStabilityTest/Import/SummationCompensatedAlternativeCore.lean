import NumStability.Algorithms.Summation.Compensated.Alternative.Core

/-!
# Alternative compensated-summation core smoke test

Checks the reusable execution API without importing error bounds, source
correspondence, or the complete compensated family.
-/

#check NumStability.AlternativeCompensatedStepTrace
#check NumStability.AlternativeCompensatedStepTrace.nextSum
#check NumStability.alternativeCompensatedPrefixSum
#check NumStability.fl_alternativeCompensatedSum
#check NumStability.fl_alternativeCompensatedSum_eq_add_globalCorrection
