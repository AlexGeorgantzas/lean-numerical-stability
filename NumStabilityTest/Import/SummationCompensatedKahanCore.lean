import NumStability.Algorithms.Summation.Compensated.Kahan.Core

/-!
# Kahan compensated-summation core smoke test

Checks the reusable execution API without importing finite-format refinements,
error analysis, source modules, or the complete compensated family.
-/

#check NumStability.KahanState
#check NumStability.KahanState.zero
#check NumStability.KahanStepTrace
#check NumStability.kahanStepTrace
#check NumStability.kahanStep
#check NumStability.kahanStepTrace_zero_of_exact_zero_path
#check NumStability.kahanPrefixState
#check NumStability.kahanPrefixState_one_of_exact_zero_path
#check NumStability.kahanTrace
#check NumStability.fl_kahanState
#check NumStability.fl_kahanSum
#check NumStability.fl_kahanCorrection
#check NumStability.fl_kahanState_eq_prefixState
#check NumStability.fl_kahanSum_eq_state_s
#check NumStability.fl_kahanCorrection_eq_state_e
