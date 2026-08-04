import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion

/-!
# MatrixInversion canonical-only test (D02, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D02 alone.
-/
#check @NumStability.methodA_forward_error
#check @NumStability.methodB_left_residual
#check @NumStability.methodC_forward_error
