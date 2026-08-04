import NumStability.Analysis.TestMatrices.Pascal.PascalOscillationCore

/-!
# PascalOscillationCore canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalOscillationCore`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.boolSignChangeCount_not
#check @NumStability.boolSignChangeCount_extract
#check @NumStability.pascalOscillationBoolToSign
