import NumStability.Analysis.SemiconvergentExistenceFull

/-!
# R01 historical-only import test O08

Imports exactly the historical owner `NumStability.Analysis.SemiconvergentExistenceFull` and checks its complete preserved public surface.
-/

#check NumStability.compBlock_blockContractive
#check NumStability.compBlock_quasiLower
#check NumStability.exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular
#check NumStability.matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement
#check NumStability.semiconvergent_block_form_exists_of_quasiTriangular_complement
