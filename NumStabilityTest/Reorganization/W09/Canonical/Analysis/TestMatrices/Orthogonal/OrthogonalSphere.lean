import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalSphere

/-!
# OrthogonalSphere canonical-only test (R_ORTHOGONAL, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28OrthogonalSphere`
during wave W09 and must resolve from R_ORTHOGONAL alone.
-/
#check @NumStability.OrthogonalSphere
#check @NumStability.orthogonalGroupSMulOrthogonalSphere
#check @NumStability.orthogonalGroup_action_pretransitive
