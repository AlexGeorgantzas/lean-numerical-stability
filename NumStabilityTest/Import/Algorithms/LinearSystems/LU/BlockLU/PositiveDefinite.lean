import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite

/-!
# Positive-definite block LU import smoke test

This test imports only the canonical positive-definite leaf and checks all
seven reviewed declarations.
-/

#check NumStability.blockMatrixNonsingular_of_posDef_flat
#check NumStability.finitePSD_of_isSymPosDef
#check NumStability.isRightInverse_nonsingInv_of_isSymPosDef
#check NumStability.isSymPosDef_det_ne_zero
#check NumStability.isSymPosDef_to_IsSymmetricFiniteMatrix
#check NumStability.isSymPosDef_to_matrix_posDef
#check NumStability.matrix_posDef_submatrix_of_injective
#check NumStability.matrix_posDef_to_isSymPosDef
