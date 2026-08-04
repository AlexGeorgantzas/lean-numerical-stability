import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversion

/-!
# MatrixInversion canonical-only test (D36, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D36 alone.
-/
#check @NumStability.Method2BBlockUpdateSpec
#check @NumStability.higham14_eq14_14_method2B_block_update_delta_bound
#check @NumStability.higham14_eq14_14_method2B_block_update_decomposition
