import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core

/-!
# R03 canonical-only test — `Core`

Imports exactly the canonical destination and checks all 10
routed public declarations. No historical owner import.
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
