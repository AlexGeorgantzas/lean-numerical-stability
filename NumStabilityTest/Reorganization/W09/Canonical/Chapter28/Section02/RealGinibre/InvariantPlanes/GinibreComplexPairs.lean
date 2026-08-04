import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreComplexPairs

/-!
# GinibreComplexPairs canonical-only test (S_GIN_PLANES, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs`
during wave W09 and must resolve from S_GIN_PLANES alone.
-/
#check @NumStability.complexUpperEigenvalueCount
#check @NumStability.map_complexMatrixCharpoly_conj
#check @NumStability.roots_complexMatrixCharpoly_map_conj
