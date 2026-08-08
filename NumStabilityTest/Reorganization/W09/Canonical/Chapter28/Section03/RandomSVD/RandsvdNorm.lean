import NumStability.Source.Higham.Chapter28.Section03.RandomSVD.RandsvdNorm

/-!
# RandsvdNorm canonical-only test (S_S03_RSVD, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28RandsvdNorm`
during wave W09 and must resolve from S_S03_RSVD alone.
-/
#check @NumStability.randsvdInverseMatrix
#check @NumStability.randsvdMatrix_isInverse
#check @NumStability.oneLargeSingularValues_pos
