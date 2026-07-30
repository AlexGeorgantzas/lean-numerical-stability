import NumStability.Analysis.Perturbation.LeastSquares.GramBasis

/-!
# GramBasis canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data
#check @NumStability.exists_lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_of_rectMatMulVec_injective
#check @NumStability.lsScaledAugmentedMatrix_kappa2_bounds_of_rightGram_basis_branch_data_of_rectMatMulVec_injective
