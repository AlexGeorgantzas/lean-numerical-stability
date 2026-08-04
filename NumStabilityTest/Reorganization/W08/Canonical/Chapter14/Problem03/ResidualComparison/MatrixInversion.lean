import NumStability.Source.Higham.Chapter14.Problem03.ResidualComparison.MatrixInversion

/-!
# MatrixInversion canonical-only test (D20, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D20 alone.
-/
#check @NumStability.higham14_problem14_3_left_residual_eq_mul_right_residual
#check @NumStability.higham14_problem14_3_max_residual_ratio_infNorm_le_kappa
#check @NumStability.higham14_problem14_3_right_residual_eq_mul_left_residual
