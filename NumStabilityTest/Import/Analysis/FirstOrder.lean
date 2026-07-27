import NumStability.Analysis.FirstOrder

/-!
# First-order analysis aggregate import smoke test

This deliberately imports only the pre-migration `Analysis.FirstOrder` path
and verifies that its declaration-free aggregate preserves the public surface.
-/

#check NumStability.RoundoffFamily
#check NumStability.ScalarFamilyIsBigOOne
#check NumStability.FamilyLinearRemainderLe
#check NumStability.FamilyFirstOrderLe
#check NumStability.FamilyFirstOrderLe.coefficient_of_linear_transfer_to
#check NumStability.FirstOrderLe
#check NumStability.FirstOrderLe.of_gamma_dim_mul
