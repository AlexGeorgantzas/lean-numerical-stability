import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalOscillation

/-!
# PascalOscillation canonical-only test (S_S04_PASCAL, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28PascalOscillation`
during wave W09 and must resolve from S_S04_PASCAL alone.
-/
#check @NumStability.pascalSortedEigenEquiv_apply
#check @NumStability.positiveMatrix_eigenvector_unique_up_to_smul
