import NumStability.Algorithms.TestMatrices.Higham28PascalCondition

/-!
# Higham28PascalCondition old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.abs_matrix_entry_le_opNorm2
#check @NumStability.pascalConditionTwo_log_rate
#check @NumStability.pascalMatrix_entry_le_four_pow
