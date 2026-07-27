import NumStability.Source.Higham.Chapter13.Theorem05.Recurrences

/-!
# Higham Theorem 13.5 recurrences import smoke test

This test imports only the canonical declaration-bearing source leaf.
-/

#check NumStability.blockErrorDelta
#check NumStability.blockErrorTheta
#check NumStability.blockErrorDelta_succ_succ
#check NumStability.blockErrorTheta_succ_succ
#check NumStability.blockErrorTheta_le_linear_of_step_bound
#check NumStability.blockErrorTheta_le_cubic_of_quadratic_constants
#check NumStability.higham13_theta_isBigO_cubic_of_quadratic_constants
#check NumStability.higham13_theta_conventional_isBigO_cubic
