import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem

/-!
# AugmentedSystem canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.lsScaledAugmentedDiagonalBranch_ne_zero_of_alpha_eq_div_sqrt_two
#check @NumStability.lsScaledAugmentedEigenvalue_branch_extreme_bounds_of_sigma_bounds
#check @NumStability.lsScaledAugmentedDiagonalBranch_abs_le_max_of_alpha_eq_div_sqrt_two
