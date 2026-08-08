import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedScalar

/-!
# Higham28GinibreSignedScalar old-path-only test

Imports only the historical path. Every declaration checked below moved to a
canonical module during wave W09, so this compiles only if the compatibility
module still re-exports it under its original name.
-/
#check @NumStability.ginibreCharacteristicProductKernel
#check @NumStability.tendsto_pow_mul_exp_mul_sub_sq_pow
#check @NumStability.tendsto_pow_mul_exp_neg_sq_div_two
