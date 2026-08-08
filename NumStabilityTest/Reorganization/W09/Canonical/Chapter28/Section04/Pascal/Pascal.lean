import NumStability.Source.Higham.Chapter28.Section04.Pascal.Pascal

/-!
# Pascal canonical-only test (S_S04_PASCAL, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.TestMatrices.Higham28Pascal`
during wave W09 and must resolve from S_S04_PASCAL alone.
-/
#check @NumStability.rotatedSignedPascal
#check @NumStability.rotatedSignedPascal_apply
#check @NumStability.pascalIdentityCubeRootCandidate
