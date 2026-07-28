import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement

/-!
# Block LU Schur-complement import smoke test

This test imports only the canonical Schur-complement leaf and checks all four
reviewed declarations.
-/

#check NumStability.blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur
#check NumStability.blockSchur
#check NumStability.det_ne_zero_blockMatrixFlatFin_blockSchur_of_first_split_invertible
#check NumStability.maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible
