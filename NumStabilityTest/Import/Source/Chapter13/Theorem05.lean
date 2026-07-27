import NumStability.Source.Higham.Chapter13.Theorem05

/-!
# Higham Theorem 13.5 aggregate import smoke test

This test imports only the canonical theorem-family aggregate.
-/

#check NumStability.blockErrorDelta
#check NumStability.blockErrorTheta
#check NumStability.blockErrorTheta_le_cubic_of_quadratic_constants
#check NumStability.higham13_theta_conventional_isBigO_cubic
