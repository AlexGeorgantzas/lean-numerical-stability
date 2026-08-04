import NumStability.Algorithms.MatrixInversion

/-!
# W11 historical compatibility through MatrixInversion

W11 consumes W08 through the historical `MatrixInversion` surface across
nineteen typed union edges. W08 does not edit W11; instead it keeps that exact
surface resolvable from the historical path. This test imports only
`NumStability.Algorithms.MatrixInversion` and checks both a relocated declaration and a retained one, so either a
lost re-export or a lost retention would fail here.
-/
#check @NumStability.Method2Spec
#check @NumStability.MatProdError
#check @NumStability.higham14_problem14_12_peiMatrix_det
