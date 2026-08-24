import NumStability.Algorithms.TestMatrices.Higham28PascalSpectral

/-!
# R09 old_only test

isolated historical import preserves the exact supported declaration surface
-/

#check @NumStability.opNorm2_pascalInverseMatrix_eq_inv_smallestEigenvalue
#check @NumStability.opNorm2_pascalOptimalSingularizingPerturbation
#check @NumStability.pascalOptimalPerturbation_is_operator2_minimal
#check @NumStability.pascal_singularizing_perturbation_norm_lower_bound
