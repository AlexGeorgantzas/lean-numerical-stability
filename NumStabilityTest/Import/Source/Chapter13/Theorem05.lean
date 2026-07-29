import NumStability.Source.Higham.Chapter13.Theorem05

/-!
# Higham Theorem 13.5 aggregate import smoke test

This test imports only the canonical theorem-family aggregate.
-/

#check NumStability.blockErrorDelta
#check NumStability.blockErrorTheta
#check NumStability.blockErrorTheta_le_cubic_of_quadratic_constants
#check NumStability.higham13_theta_conventional_isBigO_cubic

#check NumStability.dhs_block_lu_factorization_twoBudget_firstOrder
#check NumStability.dhs_schur_update_firstOrder
#check NumStability.higham13_eq13_10_from_subtraction_spec
#check NumStability.higham13_eq13_11_from_matmul_subtraction_specs
