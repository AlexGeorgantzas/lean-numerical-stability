import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalFibers

/-!
# OrthogonalFibers canonical-only test (R_ORTHOGONAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28OrthogonalFibers`
during wave W09 and must resolve from R_ORTHOGONAL alone.
-/
#check @NumStability.stewartFirstSection
#check @NumStability.stewartSphereSection
#check @NumStability.orthogonalTailExtract
