import NumStability.Algorithms.LeastSquares.Higham20QuantitativeProse

/-!
# Higham20QuantitativeProse historical import smoke test

Imports only the historical path, proving the retained compatibility
wrapper still resolves its original declarations.
-/

#check @NumStability.higham20ComputableResidual
#check @NumStability.higham20_cond2Transpose_le_card_mul_kappa2
#check @NumStability.higham20_lambdaStar_neg_of_b_not_mem_range
