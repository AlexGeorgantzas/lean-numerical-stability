import NumStability.Algorithms.LU.GrowthFactor

/-!
# Historical GrowthFactor old-only import smoke test

This test deliberately imports only the historical GrowthFactor path and
verifies that its max-entry surface remains available after extraction.
-/

#check NumStability.maxEntryNorm
#check NumStability.entry_le_maxEntryNorm
#check NumStability.maxEntryNorm_submatrix_le
#check NumStability.infNorm_le_card_mul_maxEntryNorm
#check NumStability.growthFactorEntry
#check NumStability.growth_factor_entry_lower_bound
