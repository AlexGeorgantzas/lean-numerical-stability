import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Entrywise maximum matrix norms import smoke test

This test imports only the canonical declaration-bearing leaf.
-/

#check NumStability.maxEntryNorm
#check NumStability.maxEntryNormRect
#check NumStability.maxEntryNorm_submatrix_le
#check NumStability.maxEntryNormRect_rectMatMul_le
#check NumStability.maxEntryNorm_matrix_mul_le_infNorm_mul_maxEntryNorm
#check NumStability.inv_infNorm_le_maxEntryNorm_of_isRightInverse
#check NumStability.maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound
