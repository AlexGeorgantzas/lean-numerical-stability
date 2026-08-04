import NumStability.Analysis.TestMatrices.Pascal.PascalDualFlag

/-!
# PascalDualFlag canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalDualFlag`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.pascalOscillationFRange
#check @NumStability.pascalOscillationFRange_card
#check @NumStability.pascalOscillationInsertedRows
