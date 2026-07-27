import NumStability.Analysis.FirstOrder.FixedPrecision

/-!
# Fixed-precision first-order bounds import smoke test

This test imports only the canonical declaration-bearing leaf.
-/

#check NumStability.FirstOrderLe
#check NumStability.FirstOrderLe.max
#check NumStability.FirstOrderLe.mul_is_secondOrder
#check NumStability.FirstOrderLe.finset_univ_sup'
#check NumStability.FirstOrderLe.of_gamma_dim_mul
#check NumStability.FirstOrderLe.of_gamma_sq_dim_mul
