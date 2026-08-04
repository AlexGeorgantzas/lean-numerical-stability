import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.MatrixInversion

/-!
# MatrixInversion canonical-only test (D22, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D22 alone.
-/
#check @NumStability.higham14_inverseLeftResidual_mulVec_add_self
#check @NumStability.higham14_problem14_5_forward_error_of_residual_bound
#check @NumStability.higham14_problem14_5_left_inverse_solve_residual_bound
