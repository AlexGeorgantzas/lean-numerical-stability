import NumStability.Source.Higham.Chapter14.Equation34.DeterminantFromLU.MatrixInversion

/-!
# MatrixInversion canonical-only test (D16, source)

Imports exactly one canonical module, so no sibling import can supply the
declarations checked below. They moved here from
`NumStability.Algorithms.MatrixInversion`
during wave W08 and must resolve from D16 alone.
-/
#check @NumStability.higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec
#check @NumStability.higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec
#check @NumStability.higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec
