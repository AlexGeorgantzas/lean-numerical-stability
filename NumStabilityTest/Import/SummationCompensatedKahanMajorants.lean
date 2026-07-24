import NumStability.Algorithms.Summation.Compensated.Kahan.Majorants

/-!
# Kahan majorants smoke test

Checks the canonical local and prefix absolute-majorant API without importing
the coefficient engines, finite-format layer, or source modules.
-/

#check NumStability.kahanTrace_e_abs_le
#check NumStability.kahanTrace_e_abs_le_split
#check NumStability.kahanStepDeltaWitness_s_abs_le_inputMajorants
#check NumStability.kahanCorrectionAbsMajorant
#check NumStability.kahanCorrectionAbsMajorant_nonneg
#check NumStability.kahanPrefixState_e_abs_le_correctionMajorant
#check NumStability.kahanInputAbsMajorant
#check NumStability.kahanInputAbsMajorant_nonneg
#check NumStability.kahanPrefixState_abs_le_inputMajorant
#check NumStability.kahanPrefixState_s_abs_le_inputMajorant
#check NumStability.kahanPrefixState_e_abs_le_inputMajorant
