import NumStability.Analysis.TestMatrices.Pascal.PascalSpectral

/-!
# PascalSpectral canonical-only test (R_PASCAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalSpectral`
during wave W09 and must resolve from R_PASCAL alone.
-/
#check @NumStability.pascalMatrix_isSymmetricFiniteMatrix
