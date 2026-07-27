import NumStability.Algorithms.LU.BlockLU

/-!
# Historical BlockLU old-only import smoke test

This test deliberately imports only the historical BlockLU path. It verifies
that Phase 12A extraction preserves representatives from every migrated
surface formerly declared by or available through that module.
-/

#check NumStability.FirstOrderLe
#check NumStability.maxEntryNorm
#check NumStability.maxEntryNormRect
#check NumStability.blockMaxNorm
#check NumStability.MatMulFirstOrderSpec
#check NumStability.blockErrorDelta
#check NumStability.higham13_theta_conventional_isBigO_cubic
