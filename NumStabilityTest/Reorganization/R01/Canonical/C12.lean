import NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.QuasiTriangularBlockForm

/-!
# R01 canonical-only import test C12

Imports exactly the frozen canonical leaf `NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.QuasiTriangularBlockForm` and checks every public declaration routed there.
-/

#check NumStability.compBlock_blockContractive
#check NumStability.compBlock_quasiLower
#check NumStability.exists_diag_infNorm_conj_lt_one_of_quasiUpperTriangular
#check NumStability.matPow_G_tendsto_oneEigenProjector_of_quasiTriangular_complement
#check NumStability.semiconvergent_block_form_exists_of_quasiTriangular_complement
