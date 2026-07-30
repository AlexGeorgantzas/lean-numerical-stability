import NumStability.Source.Higham.Chapter20.Prose.Quantitative

/-!
# Prose.Quantitative canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.higham20ComputableResidual
#check @NumStability.higham20_cond2Transpose_le_card_mul_kappa2
#check @NumStability.higham20_lambdaStar_neg_of_b_not_mem_range
