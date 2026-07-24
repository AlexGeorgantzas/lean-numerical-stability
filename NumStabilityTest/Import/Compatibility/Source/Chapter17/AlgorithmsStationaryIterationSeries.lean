import NumStability.Algorithms.StationaryIterationSeries

/-!
# Historical Chapter 17 stationary-series import smoke test

This old-only smoke checks one declaration from every canonical target of the
historical multi-target wrapper, without importing the Chapter 17 umbrella.
-/

#check NumStability.tsum_infNorm_matPow_le
#check NumStability.higham17_problem17_1
#check NumStability.partialSumBound_cALiteral
#check NumStability.literal_norm_form_forward_bound
#check NumStability.literal_norm_form_jacobi_forward_bound
#check NumStability.literal_norm_form_gaussSeidel_forward_bound
#check NumStability.residualSigmaTsum_le_diagonalizable_max_bound_of_infNorm_bound
