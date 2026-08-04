import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalSpectral

/-!
# PascalSpectral canonical-only test (S_S04_PASCAL, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalSpectral`
during wave W09 and must resolve from S_S04_PASCAL alone.
-/
#check @NumStability.pascalInverseMatrix
#check @NumStability.opNorm2_transpose_eq
#check @NumStability.opNorm2_matrix_mul_le
