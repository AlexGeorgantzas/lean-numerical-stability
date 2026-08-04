import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates

/-!
# OrthogonalCoordinates canonical-only test (R_ORTHOGONAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28OrthogonalCoordinates`
during wave W09 and must resolve from R_ORTHOGONAL alone.
-/
#check @NumStability.orthogonalFirstRow
#check @NumStability.orthogonalFirstColumn
#check @NumStability.orthogonalSphereNonempty
