import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion

/-!
# MatrixInversion canonical-only test (D04, reusable)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D04 alone.
-/
#check @NumStability.ideal_forward_error
#check @NumStability.ideal_left_residual
#check @NumStability.inverseLeftResidual
