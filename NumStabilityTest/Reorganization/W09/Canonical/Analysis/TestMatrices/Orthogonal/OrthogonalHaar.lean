import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalHaar

/-!
# OrthogonalHaar canonical-only test (R_ORTHOGONAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28OrthogonalHaar`
during wave W09 and must resolve from R_ORTHOGONAL alone.
-/
#check @NumStability.RealOrthogonalGroup
#check @NumStability.normalizedOrthogonalHaar
#check @NumStability.realSquareMatrixBorelSpace
