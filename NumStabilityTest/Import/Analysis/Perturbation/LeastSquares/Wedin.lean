import NumStability.Analysis.Perturbation.LeastSquares.Wedin

/-!
# Wedin canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20_wedin_domain_null_projection_factorization
#check @NumStability.higham20_wedin_solution_data_domain_null_vecNorm2Sq
#check @NumStability.higham20_wedin_pseudoinverse_difference_decomposition
