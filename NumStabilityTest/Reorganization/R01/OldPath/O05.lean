import NumStability.Algorithms.StationaryIterationSemiconvergentExistence

/-!
# R01 historical-only import test O05

Imports exactly the historical owner `NumStability.Algorithms.StationaryIterationSemiconvergentExistence` and checks its complete preserved public surface.
-/

#check NumStability.X_inv_G_X_eq_blockJ
#check NumStability.blockJ
#check NumStability.blockJ_bottom
#check NumStability.blockJ_bottom_row_sum_le
#check NumStability.blockJ_cross
#check NumStability.blockJ_top
#check NumStability.matMul_G_X_eq_X_blockJ
#check NumStability.matPow_G_tendsto_oneEigenProjector_of_block_data
#check NumStability.semiconvergent_block_form_exists
#check NumStability.singular_error_split_semiconvergent_of_block_data
