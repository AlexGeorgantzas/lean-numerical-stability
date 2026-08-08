import NumStability.Analysis.TestMatrices.Pascal.Basic

/-!
# Basic canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.pascalLower
#check @NumStability.pascalMatrix
#check @NumStability.signedPascal
