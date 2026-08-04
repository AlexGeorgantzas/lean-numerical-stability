import NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion

/-!
# MatrixInversion canonical-only test (D06, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D06 alone.
-/
#check @NumStability.Method2Spec
#check @NumStability.BlockMethod1BSpec
#check @NumStability.Method2StrictTailKernelSpec
