import NumStability.Algorithms.LU.Doolittle

/-!
# R03 historical-only test — `Doolittle`

Imports exactly the historical path; checks its preserved public
surface (10 declarations).
-/

#check @NumStability.DoolittleDenseLoopAbsBudgetCertificate.of_literal_doolittle_exact_target_gaps
#check @NumStability.DoolittleDenseLoopAbsBudgetCertificate.to_DoolittleLU
#check @NumStability.DoolittleDenseLoopAbsBudgetCertificate.to_LUBackwardError
#check @NumStability.DoolittleDenseLoopCertificate.to_DoolittleLU
#check @NumStability.DoolittleDenseLoopCertificate.to_LUBackwardError
#check @NumStability.DoolittleLU.to_LUBackwardError
#check @NumStability.doolittleLExactProductMargin_of_exactTarget_gap
#check @NumStability.doolittleLExactProductNumeratorMargin_of_exactTarget_gap
#check @NumStability.doolittleUExactProductMargin_of_exactTarget_gap
#check @NumStability.doolittle_backward_error
