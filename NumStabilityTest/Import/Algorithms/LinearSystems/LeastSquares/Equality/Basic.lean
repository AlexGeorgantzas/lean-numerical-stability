import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic

/-!
# Equality-constrained least squares basics canonical-only import smoke test

Imports exactly one canonical module and checks representative public declarations.
-/

#check @NumStability.theorem20_7_finRectProdUniv_nonempty_of_pos
#check @NumStability.LSEFullRowRank.rightInverse
#check @NumStability.theorem20_10_householder_component_max_gamma_le_componentUnitRoundoffCoefficient_mul_u_of_small
#check @NumStability.continuous_lsObjective
#check @NumStability.continuous_lseConstraintResidual_apply
#check @NumStability.finAppend_left_right
#check @NumStability.matMulVec_orthogonal_mul_transpose
#check @NumStability.matMulVec_orthogonal_transpose_mul
#check @NumStability.matMulVec_zero
#check @NumStability.rectMatMulVec_zero
#check @NumStability.vecNorm2Sq_append
