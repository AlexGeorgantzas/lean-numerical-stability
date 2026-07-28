import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance

/-!
# Block diagonal dominance import smoke test

This test imports only the canonical declaration-bearing leaf and checks all
eight reviewed declarations.
-/

#check NumStability.IsBlockDiagDomCol
#check NumStability.IsBlockDiagDomRow
#check NumStability.blockDiagDomGamma
#check NumStability.blockDiagDomRowGamma
#check NumStability.blockDiagDomRowGamma_eq_colTranspose_gamma
#check NumStability.isBlockDiagDomCol_iff_gamma_nonneg
#check NumStability.isBlockDiagDomRow_iff_col_transpose
#check NumStability.isBlockDiagDomRow_iff_gamma_nonneg
