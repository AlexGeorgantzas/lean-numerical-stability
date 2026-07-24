import NumStability.Algorithms.Summation.Compensated.FastTwoSum

/-!
# Compensated FastTwoSum reusable-leaf smoke test

This test imports the finite correction-formula certificate API without the
complete compensated family or any Higham source module.
-/

#check NumStability.FastTwoSumFiniteCertificate
#check NumStability.finiteCorrectionFormulaTrace_exact_of_base2_abs_le
