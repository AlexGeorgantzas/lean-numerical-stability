import NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion
import NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation34.DeterminantFromLU.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion
import NumStability.Source.Higham.Chapter14.Equation36.HymanDeterminant.MatrixInversion
import NumStability.Source.Higham.Chapter14.Problem03.ResidualComparison.MatrixInversion

/-!
# MatrixInversion mixed-owner routing

`NumStability.Algorithms.MatrixInversion` is one of the three owners B0007 requires to be split
declaration by declaration. This test imports both sides of that cut and
checks a declaration from each, so a wholesale reclassification in either
direction would fail to compile.
-/
#check @NumStability.methodA_forward_error
#check @NumStability.methodAComputedInverse
#check @NumStability.ideal_forward_error
#check @NumStability.triInv_method1_forward_error
#check @NumStability.higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec
#check @NumStability.higham14_hymanSchur
#check @NumStability.higham14_eq14_36_hyman_det_cyclic_block
#check @NumStability.higham14_problem14_3_left_residual_eq_mul_right_residual
