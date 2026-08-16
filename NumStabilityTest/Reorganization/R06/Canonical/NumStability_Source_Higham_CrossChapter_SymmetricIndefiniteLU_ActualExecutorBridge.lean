import NumStability.Source.Higham.CrossChapter.SymmetricIndefiniteLU.ActualExecutorBridge

/-!
# R06 canonical-only test — `ActualExecutorBridge`

Imports exactly the canonical destination and checks all 7
routed public declarations. No historical owner import.
-/

#check @NumStability.higham11_7_actualSolveCoefficient
#check @NumStability.higham11_7_actualTotalEta
#check @NumStability.higham11_7_forwardError_family_condition_product_of_actual_block_ldlt_executor
#check @NumStability.higham11_7_forwardError_family_of_actual_block_ldlt_executor
#check @NumStability.higham11_7_forwardError_of_actual_block_ldlt_executor
#check @NumStability.higham11_7_permutedAbsLDLT_refl_eq_productEntry
#check @NumStability.higham11_7_perturbed_product_envelopeCondition_le_totalEnvelope
