import NumStability.Algorithms.LeastSquares.LSE

/-!
# LSE historical import smoke test

Imports only the historical path and checks declarations from every canonical destination.
-/

#check @NumStability.theorem20_7_finRectProdUniv_nonempty_of_pos
#check @NumStability.gqrAQBlock
#check @NumStability.LSEKKTSystem
#check @NumStability.theorem20_7_alpha_le_of_entry_growth
#check @NumStability.theorem20_8MaxRelativePerturbation
#check @NumStability.GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_same_d
#check @NumStability.theorem20_8_nullspace_reduced_wedinResidualRHS_le_of_lse_minimizers
#check @NumStability.Theorem20_10.orthogonal_matMulVec_injective
#check @NumStability.continuous_lsObjective
#check @NumStability.continuous_lseConstraintResidual_apply
#check @NumStability.finAppend_left_right
#check @NumStability.matMulVec_orthogonal_mul_transpose
#check @NumStability.matMulVec_orthogonal_transpose_mul
#check @NumStability.matMulVec_zero
#check @NumStability.rectMatMulVec_zero
#check @NumStability.vecNorm2Sq_append
