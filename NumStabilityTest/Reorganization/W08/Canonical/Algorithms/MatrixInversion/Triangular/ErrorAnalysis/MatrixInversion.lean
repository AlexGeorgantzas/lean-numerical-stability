import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion

/-!
# MatrixInversion canonical-only test (D05, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D05 alone.
-/
#check @NumStability.triInv_method1_forward_error
#check @NumStability.triInv_method2_left_residual
#check @NumStability.triInv_method1_normwise_error
