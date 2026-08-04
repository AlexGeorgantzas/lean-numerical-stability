import NumStability.Analysis.TestMatrices.Pascal.PascalOscillation

/-!
# PascalOscillation canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalOscillation`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.initialPowerset
#check @NumStability.IsSignCompletion
#check @NumStability.compoundMatrix_one
