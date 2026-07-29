import NumStability.Algorithms.LinearSystems.LeastSquares.MGS

/-!
# MGS canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.MGSAugmentedLSFactorization
#check @NumStability.MGSAugmentedLSFactorization.residual_eq
#check @NumStability.MGSAugmentedLSFactorization.objective_eq_top_plus_rho_sq
