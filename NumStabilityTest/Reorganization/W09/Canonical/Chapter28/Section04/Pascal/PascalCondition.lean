import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalCondition

/-!
# PascalCondition canonical-only test (S_S04_PASCAL, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalCondition`
during wave W09 and must resolve from S_S04_PASCAL alone.
-/
#check @NumStability.abs_matrix_entry_le_opNorm2
#check @NumStability.pascalConditionTwo_log_rate
#check @NumStability.pascalMatrix_entry_le_four_pow
